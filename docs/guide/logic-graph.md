# Translating between logics

The kit moves a formula from one logic to another along a **graph of nine one-way translations** ({mod}`unicode_fol_kit.comorphism`). You reach the graph through logic *values* ({mod}`unicode_fol_kit.logic`: `FOL`, `MODAL`, `MSFOL`, …) or through `api.translate`. What comes back is never just a term. It is a term, the **side axioms** that term needs before it answers anything, and a statement of what the translation **guarantees**. This page is about that triple and why it exists.

## A translation is not a subtype

The tempting design is a hierarchy: many-sorted logic "is a" first-order logic, modal logic "is a" first-order logic, and a value may flow upward wherever the target is expected. The kit does not do that, because the image of a translation usually does not answer a question by itself. The smallest case is a formula that is valid in the kit's many-sorted semantics:

```python
from unicode_fol_kit import MSFLParser, api
from unicode_fol_kit.logic import FOL, MSFOL

f = MSFLParser(many_sorted=True).parse("(∀x:Human M(x)) → ∃x:Human M(x)")
api.prove(f).status  # → 'proved'
```

If every `Human` is `M`, then some `Human` is, because the kit's many-sorted logic never lets a sort be empty (see the many-sorted section of {doc}`classical-reasoning`). Now convert it. `MSFOL(f)` wraps `f` as a sentence of the many-sorted logic, and `FOL(…)` converts that sentence to classical first-order logic:

```python
image = FOL(MSFOL(f))
image.term.to_unicode_str()  # → '∀x (Human(x) → M(x)) → ∃x (Human(x) ∧ M(x))'
api.prove(image.term).status  # → 'refuted'
```

The image is **not valid**: a structure in which `Human` is empty satisfies the antecedent vacuously and falsifies the consequent. Non-emptiness was a property of the semantics, and the translation moved it out of the formula. It does not disappear. It comes back as a side axiom, next to the term:

```python
[a.to_unicode_str() for a in image.axioms]  # → ['∃x0 Human(x0)']
api.prove(image.term, image.axioms).status  # → 'proved'
api.prove(image).status  # → 'proved'
```

The first `prove` passes the axioms as premises by hand. The second hands over the whole `Sentence`, and `api.prove` adds its axioms as premises itself. The bare `image.term` is the one call that gets the question wrong, and nothing in its type says so.

A subtype relation would make that call the normal one. A translation differs from an upcast in four ways, and each of them shows up in the edge table below:

- **It changes the signature.** The standard translation of modal logic appends a world argument to every predicate (`P` becomes `P(w)`), and an ALC concept becomes a formula with one free individual variable `x`.
- **It is defined on a fragment.** `Until` has no first-order form, a propositional modal formula cannot contain a quantifier or an equality atom, a multi-role concept has no image in modal `K`, and a formula outside the image of `drs_to_fol` has no DRS. The edges refuse these by name rather than approximate them.
- **It has side conditions.** Sort non-emptiness, the membership of a sorted constant in its sort, subsort inclusions, the frame conditions of a modal system, the domain regime of a quantified modal logic: each is a property of the source semantics that the image does not state.
- **It may preserve less than everything.** Łukasiewicz logic collapses onto classical logic by a two-valued projection, and a composed path is only as strong as its weakest edge.

## Why the axioms are separate premises

There are two obvious ways to keep an axiom with its formula: conjoin it onto the formula, or put it in front as a conditional. Both give wrong answers, in opposite directions.

```python
from unicode_fol_kit import And, Implies, Not

(axiom,) = image.axioms
api.prove(And(axiom, image.term)).status  # → 'refuted'
api.prove(Implies(axiom, image.term)).status  # → 'proved'
```

The conjunction asks the prover to establish the axiom as well, and the axiom is not valid, so a valid formula comes back refuted. The conditional gets validity right, but it is satisfied by the structure in which the axiom fails, so it makes an unsatisfiable formula satisfiable:

```python
g = MSFLParser(many_sorted=True).parse("∀x:Human (P(x) ∧ ¬P(x))")
translated = FOL(MSFOL(g))
api.prove(Not(g)).status  # → 'proved'
api.prove(Not(Implies(translated.axioms[0], translated.term))).status  # → 'refuted'
api.prove(Not(translated.term), translated.axioms).status  # → 'proved'
```

`g` is unsatisfiable, since a `Human` would have to be both `P` and not `P`, so `Not(g)` is valid. The sorted formula says so, and so does the image with its axiom as a **separate premise**. The conditional form claims `g` is satisfiable.

A separate premise is read the same way under every polarity. For an entailment or validity question it is one more premise. For a satisfiability question it is one more asserted conjunct. It is never part of the formula, so it cannot end up under a negation or be required of the goal. That is the rule the whole graph follows: `TranslationResult.axioms` and `Sentence.axioms` are **separate premises of the question you ask about the image**.

## The nine edges

`DEFAULT_REGISTRY.edges()` lists them. The *guarantee* column is what the registry declares for the edge (the vocabulary is below); for an edge with side axioms it is declared for the image **together with** those axioms.

| Edge | From → to | Guarantee | Side axioms | Options | Refuses, or note |
| --- | --- | --- | --- | --- | --- |
| `standard_translation` | `modal` → `fol` | faithful | frame conditions of every relation the image mentions, and the membership `∀v0 S(c, v0)` of every sorted constant `c:S` of the formula | `frame`, `systems`, `temporal_closure` | `Until`/`Since` (not first-order definable), quantifiers (use `qml`), equality atoms, a frame system with no first-order condition (`GL`, `S4.1`, `Grz`) |
| `qml_translate` | `qml` → `fol` | faithful | the World/Object sort discipline, the domain regime of `mode=`, the frame conditions, the membership of every sorted constant in its sort at every world | `mode`, `frame`, `systems`, `bridges`, `temporal_closure` | `Until`/`Since`, the `↓` binder, `@` and nominals, a frame system with no first-order condition |
| `to_fol` | `msfol` → `fol` | faithful | one non-emptiness sentence per sort, one membership atom `S(c)` per sorted constant `c:S` (without it the image forgets that `c` is in `S`); with `signature=`, one inclusion per declared subsort edge | `signature` | no restriction; the axioms are the point |
| `to_msfol` | `fuzzy` → `msfol` | **lossy** | none | none | not truth-preserving: weak and strong conjunction get the same image, so it is sound only on crisp `{0,1}` valuations |
| `drs_to_fol` | `drs` → `fol` | faithful | none | none | a DRS is a closed box, so the image is a sentence with no free anchor |
| `fol_to_drs` | `fol` → `drs` | faithful | none | none | a formula outside the image of `drs_to_fol` (`FolToDrsError`) |
| `concept_to_modal` | `alc` → `modal` | faithful | none | none | concepts with more than one role, number restrictions, inverse roles |
| `concept_to_fol` | `alc` → `fol` | faithful | none | none | the concept is read against the **empty** knowledge base, with `x` free; a concept with a **data restriction** (`DataExists` and its siblings) is refused by name (`UnsupportedDatatypeError`), since the sorts and the datatype lattice of its image are side axioms of a *knowledge base*: ask `dl.kb_to_fol(…, query=[concept])` |
| `dependence_to_eso` | `team` → `eso` | faithful | none | none | sentences only; a dependence atom must guard its own `∃`; `∨` anywhere in a sentence that also has a dependence atom |

The edges as a graph, in the registry's own labels:

```text
fuzzy → msfol → fol ⇄ drs
qml   → fol
modal → fol
alc   → fol
alc   → modal
team  → eso
```

`api.translate(term, source, target)` and `Sentence.to(target)` follow the **shortest** path (breadth-first, neighbours in sorted label order, so ties always resolve the same way) and compose the edges on it. `fuzzy` reaches `fol` in two steps. `alc` reaches `fol` directly even though it also reaches it through `modal`. There is no edge back out of `fol` except to `drs`, and `team → eso` is a component of its own. A pair with no path raises `ValueError`, and an unknown label is reported together with the labels the registry knows.

The refusals in the last column are real exceptions, each naming what it refused and what to use instead. Two from the standard translation (equality has [its own section](#equality-is-not-an-ordinary-atom-here) below), one from `alc → modal`:

```python
from textwrap import fill
from unicode_fol_kit.comorphism import DEFAULT_REGISTRY
from unicode_fol_kit.dl import parse_concept

m = MSFLParser(modal=True)
cases = [("quantifier", m.parse("∀x □P(x)"), {}),
         ("Löb frame", m.parse("□P → P"), {"frame": "GL"})]
for label, term, options in cases:
    try:
        DEFAULT_REGISTRY.translate(term, "modal", "fol", **options)
    except Exception as exc:
        print(f"{label}: {type(exc).__name__}")
        print(fill(str(exc), 88, initial_indent="  ", subsequent_indent="  "))
# → quantifier: NotImplementedError
# →   standard_translation: Quantifier is not supported — the standard translation here
# →   covers the propositional modal fragment only. For quantified (first-order) modal logic
# →   with object domains use unicode_fol_kit.fol.qml (qml_translate / qml_is_valid, the FO
# →   shallow embedding with explicit constant/varying/increasing/decreasing domain
# →   regimes).
# → Löb frame: UnsupportedFrameCondition
# →   frame_axioms: the frame condition 'loeb' has no first-order frame condition, so the
# →   standard translation cannot express 'GL' (Löb, S4.1 and Grz need the higher-order
# →   routes: hol.isabelle_modal / hol.thf_modal, or the finite-frame enumerator
# →   atp.kripke_enum)
try:
    DEFAULT_REGISTRY.translate(parse_concept("∃r.A ⊓ ∃s.B"), "alc", "modal")
except NotImplementedError as exc:
    print(fill(str(exc), 88))
# → concept_to_modal: concept uses 2 distinct roles ['r', 's']; propositional modal K has
# → exactly ONE accessibility relation, so per-role restrictions (∃r.C / ∀r.C for different
# → r) cannot be faithfully rendered as Box/Diamond — there is no honest way to recover
# → which role a given □/◇ came from. Use concept_to_fol instead: it has no such limitation,
# → since a role is just another binary FOL predicate r(x, y) and FOL scales to any number
# → of them.
```

## Converting

### Logic values and `Sentence`

A logic value is callable. Called on a **bare term** it wraps it as a `Sentence` of that logic and does nothing else. Called on a **`Sentence`** it converts, through the registry:

```python
from unicode_fol_kit.logic import MODAL

s = MODAL(m.parse("□P → P"))
s  # → Sentence[modal](□P → P, guarantee=faithful)
t = FOL(s)
t.term.to_unicode_str()  # → '∀w0 (R(w, w0) → P(w0)) → P(w)'
(t.logic, t.path, t.guarantee, t.axioms)  # → ('fol', ('standard_translation',), 'faithful', ())
```

A `Sentence` holds six fields: `term`, `logic`, `axioms`, `guarantee`, `path` (the edges the conversion took) and `note` (the conventions those edges documented; `with_note(text)` returns a copy with one more appended). Here the note says that the image is anchored at the **free world variable** `w`: close it universally for a validity question and existentially for a satisfiability question. A validity question needs no explicit closure, because an open formula is valid exactly when its closure is.

The same term converts differently under different options, and only the axioms change:

```python
for frame in ("K", "T", "S4"):
    converted = FOL(s, frame=frame)
    print(frame, len(converted.axioms), api.prove(converted).status)
# → K 0 refuted
# → T 1 proved
# → S4 2 proved
```

`□P → P` is valid exactly on reflexive frames. The three images are the same formula; `T` and `S4` supply the reflexivity axiom as a premise, and `K` supplies nothing.

`Sentence.to(label)` is the same conversion by label, and `LOGICS` maps every label (`"fol"`, `"msfol"`, `"modal"`, `"qml"`, `"alc"`, `"drs"`, `"team"`, `"eso"`, `"fuzzy"`) to its logic value. Converting to the logic a sentence is already in returns the sentence unchanged.

### Options are routed, never ignored

Options go to the edges on the path that declare them. An option that **no** edge on the path declares raises, so a typo cannot turn into a different question. Wrapping takes no options at all:

```python
from textwrap import fill

try:
    FOL(s, speed=3)
except ValueError as exc:
    print(fill(str(exc), 88))
# → translate: option(s) ['speed'] are accepted by no edge on 'modal'→'fol' (path
# → ['standard_translation'], accepted: ['frame', 'systems', 'temporal_closure'])
try:
    MODAL(m.parse("□P"), frame="S4")
except TypeError as exc:
    print(exc)
# → modal: options ['frame'] apply to a CONVERSION; wrapping a bare term takes none
```

`frame` and `systems` change the axioms but not the translation. `frame` is the system of the alethic relation `R`, and `systems` maps an agent-indexed family (`"epistemic"`, `"doxastic"`, `"assertive"`, `"bouletic"`) to a system for it. `signature` supplies the subsort hierarchy, which is not in the term at all. `mode` and `bridges` belong to the quantified modal edge.

```python
from unicode_fol_kit import Signature
from unicode_fol_kit.logic import QML

q = m.parse("◇∃x A(x) → ∃x ◇A(x)")
[(mode, api.prove(FOL(QML(q), mode=mode)).status) for mode in ("constant", "varying")]  # → [('constant', 'proved'), ('varying', 'refuted')]
sorted_parser = MSFLParser(many_sorted=True)
h = sorted_parser.parse("(∀x:Animal P(x)) → ∀y:Human P(y)")
sig = Signature(sorts=("Animal", "Human"), subsorts={"Human": frozenset({"Animal"})})
[api.prove(FOL(MSFOL(h), **options)).status for options in ({}, {"signature": sig})]  # → ['refuted', 'proved']
```

The first list asks the Barcan formula under constant and under varying domains: the answer differs, and `mode=` changes the domain axioms. The last list is valid only with the subsort edge `Human ⊑ Animal`, which the term itself cannot know about.

### `api.translate` and the registry

`api.translate(term, source, target)` returns a `TranslationResult` with the same information as a `Sentence` (`result`, `axioms`, `guarantee`, `path`, `lossy`, `note`), and `to_dict()` gives the JSON form. Options are keyword arguments and are routed exactly as for a logic value; `api.translate` is a thin wrapper over `DEFAULT_REGISTRY.translate(term, source, target, **options)`.

```python
r = api.translate(f, "msfol", "fol")
(r.path, r.guarantee, r.lossy, len(r.axioms))  # → (('to_fol',), 'faithful', False, 1)
r = api.translate(m.parse("□P → P"), "modal", "fol", frame="S4")
api.prove(r.result, r.axioms).status  # → 'proved'
r == DEFAULT_REGISTRY.translate(m.parse("□P → P"), "modal", "fol", frame="S4")  # → True
```

### What conversion refuses

`Sentence` refuses to be combined implicitly. `&`, `|` and `~` raise, between logics and within one, because combining two sentences is exactly where side axioms get lost: silently and wrongly across logics, by being dropped within one. Convert explicitly, then combine the `.term` values and pass the union of the `.axioms` as premises.

```python
from textwrap import fill

try:
    s & t
except TypeError as exc:
    print(fill(str(exc), 88))
# → Sentence: '&' is not defined on a Sentence (this one is in logic 'modal'). A Sentence is
# → a term together with the side axioms that make it mean what it meant; building a bigger
# → formula out of two of them is where those axioms get lost — across logics silently and
# → wrongly, within one logic by just being dropped. Combine the .term values with the AST's
# → own constructors and pass the union of the .axioms as premises.
```

A path whose later edge cannot express an earlier edge's side axiom is refused outright. The reflexivity axiom `∀v0 R(v0, v0)` that the frame `T` adds on `modal → fol` is not in the image of `fol → drs` (a universal needs an implication body there), so the composition cannot answer the question and says so:

```python
try:
    MODAL(m.parse("□P")).to("drs", frame="T")
except ValueError as exc:
    print(fill(str(exc), 88))
# → translate: edge 'fol_to_drs' cannot carry a side axiom of an earlier edge on
# → 'modal'→'drs'; this path cannot answer the question for this term
```

`api.prove` accepts a `Sentence` in `fol` or `msfol` and unwraps it with its axioms. A `Sentence` in any other logic is refused by name:

```python
try:
    api.prove(s)
except ValueError as exc:
    print(fill(str(exc), 88))
# → prove: the goal is a Sentence in logic 'modal', which these routes do not decide —
# → convert it first, e.g. FOL(sentence) (unicode_fol_kit.logic), and pass that
```

## Reading the guarantee

An edge declares what it preserves. The vocabulary, strongest first, is `GUARANTEES`:

| Guarantee | What transfers |
| --- | --- |
| `faithful` | a model of the source term and a model of the image are inter-convertible (pointwise, for edges with a free anchor), so every question transfers |
| `validity` | a validity or entailment question transfers once the edge's axioms are added as separate premises |
| `satisfiability` | only satisfiability transfers (for example when the anchor has to be closed existentially); a validity answer does **not** |
| `lossy` | neither; the edge's `note` says what is dropped |

A path has the **weakest** guarantee on it, because a faithful edge after a lossy one repairs nothing. `None` means some edge on the path declares no guarantee at all. That is **not** a synonym for faithful: an undeclared edge makes no promise.

```python
from unicode_fol_kit.comorphism import GUARANTEES, weakest_guarantee
from unicode_fol_kit.logic import FUZZY

GUARANTEES  # → ('faithful', 'validity', 'satisfiability', 'lossy')
weakest_guarantee(["faithful", "validity"])  # → 'validity'
print(weakest_guarantee(["faithful", None]))  # → None
fuzzy = FUZZY(MSFLParser(fuzzy=True).parse("P ⊗ Q"))
projected = FOL(fuzzy)
(projected.term.to_unicode_str(), projected.path, projected.guarantee)  # → ('P ∧ Q', ('to_msfol', 'to_fol'), 'lossy')
```

The fuzzy path is `lossy` because `to_msfol` is a two-valued projection. For the real-valued Łukasiewicz degree use the fuzzy evaluator ({doc}`fuzzy`), not this route. The default edges all declare a guarantee. An edge registered by a third party, such as the dynamic `hets:<Name>` edges from `register_hets_comorphisms`, may not, and a path through one reports `None`:

```python
from unicode_fol_kit.comorphism import Comorphism, ComorphismRegistry

registry = ComorphismRegistry()     # a private registry; register_comorphism adds to the default one
registry.register(Comorphism(name="first", source="a", target="b",
                             apply=lambda term: f"b({term})", guarantee="faithful",
                             axioms=lambda term: (f"ax({term})",)))
registry.register(Comorphism(name="second", source="b", target="c",
                             apply=lambda term: f"c({term})", guarantee="validity",
                             axioms=lambda term: (f"bx({term})",)))
registry.register(Comorphism(name="third", source="c", target="d",
                             apply=lambda term: f"d({term})"))      # declares nothing
r = registry.translate("x", "a", "c")
(r.result, r.axioms, r.guarantee)  # → ('c(b(x))', ('c(ax(x))', 'bx(b(x))'), 'validity')
print(registry.translate("x", "a", "d").guarantee)  # → None
```

Side axioms accumulate along a path. The first edge's axiom `ax(x)` is a term of `b`, so the second edge translates it (`c(ax(x))`), and the second edge adds its own, computed from the term it was handed (`bx(b(x))`). The path's guarantee is the weaker of the two declared ones, and a path through the third edge, which declares nothing, has none. An edge that sets `lossy=True` and no guarantee ends up with the guarantee `None`, not `"lossy"`; setting `lossy=True` together with a stronger guarantee raises when the edge is built.

## Frame conditions for every relation

The standard translation emits more than one accessibility relation. `□` and `◇` read `R`, the temporal operators read `T` ("henceforth") and `N` ("next"), the deontic ones read `D`, and each agent gets a relation of its own for knowledge, belief, assertion and desire. Up to and including 0.28.1 only the conditions of `R` were asserted on the hybrid route. A formula that the kit's own modal semantics validates, such as `Ⓖφ → φ` or `Ⓞφ → Ⓟφ`, came back "not valid" from `hybrid_is_valid`, a bare `False` that gave no hint the route had never been told what `T` or `D` is, while `qml_is_valid` answered `True` on the same formula. The first column below is what 0.28.1 answered, the others are what the kit answers now:

| Formula | Frame | `hybrid_is_valid`, 0.28.1 | `hybrid_is_valid`, now | `qml_is_valid` |
| --- | --- | --- | --- | --- |
| `Ⓖ(P) → P` | S5 | False | True | True |
| `Ⓖ(P) → Ⓝ(P)` | S5 | False | True | True |
| `Ⓞ(P) → Ⓟ(P)` | S5 | False | True | True |
| `□P → P` | T | True | True | True |
| `□P → P` | K | False | False | False |

```python
from unicode_fol_kit.fol.modal_translation import frame_axioms, hybrid_is_valid, relations_used
from unicode_fol_kit.fol.qml import qml_is_valid

for text in ("Ⓖ(P) → P", "Ⓞ(P) → Ⓟ(P)"):
    formula = m.parse(text)
    print(text, hybrid_is_valid(formula, "S5"), qml_is_valid(formula, frame="S5"))
# → Ⓖ(P) → P True True
# → Ⓞ(P) → Ⓟ(P) True True
```

`relations_used(formula)` names the relations the translation of `formula` mentions, and `frame_axioms(formula, frame, systems=, temporal_closure=)` returns the first-order axioms for **exactly those**. A condition on a relation the formula never mentions is noise, and on a route that reports a bare "not valid" it is noise that can change the answer.

```python
henceforth = m.parse("Ⓖ(P) → P")
sorted(relations_used(henceforth))  # → ['T']
[a.to_unicode_str() for a in frame_axioms(henceforth, "S5")]  # → ['∀v0 T(v0, v0)', '∀v0 ∀v1 ∀v2 (T(v0, v1) ∧ T(v1, v2) → T(v0, v2))']
[a.to_unicode_str() for a in frame_axioms(m.parse("Ⓞ(P) → Ⓟ(P)"), "K")]  # → ['∀v0 ∃v1 D(v0, v1)']
```

`frame` constrains only the alethic relation `R`, so `S5` adds nothing to a formula that mentions only `T`. It accepts any system of the shared frame table, `KD45` for example, and not only `K`, `T`, `S4` and `S5`. Temporal operators get a reflexive and transitive `T` by default, which is how the Kripke evaluator reads them, and, when `N` occurs too, `N ⊆ T` and the first-order half of `T ⊆ N*` (a `T`-successor is the world itself or is reached by an `N`-step first). `temporal_closure=False` drops all of these but `N ⊆ T` and turns the route into a weaker temporal logic. Deontic operators get a serial `D`, which is Standard Deontic Logic. An agent family gets **nothing** unless `systems=` asks:

```python
knowing = m.parse("K_alice P → P")
(hybrid_is_valid(knowing, "K"), hybrid_is_valid(knowing, "K", systems={"epistemic": "T"}))  # → (False, True)
api.prove(FOL(MODAL(knowing), systems={"epistemic": "T"})).status  # → 'proved'
hybrid_is_valid(henceforth, "S5", temporal_closure=False)  # → False
```

`hybrid_is_valid` and `down_is_valid` take `systems=` and `temporal_closure=` and assert the conditions of every relation the image mentions. The `modal` edge takes the same options, so `FOL(MODAL(…), systems=…)` hands `api.prove` the same conditions, as the second line above shows. A system with no first-order frame condition is refused by name from both, because this route is first-order: `GL`, `S4.1` and `Grz` need the higher-order routes in {doc}`modal`.

The same rule applies to any route that is handed the bare image. The in-process resolution prover, given the image of `Ⓖ(P) → P` alone, answers `False`, which {doc}`quantified-modal` explains as a route difference; given the frame axioms as premises it agrees with the others:

```python
from unicode_fol_kit import prove, standard_translation

image = standard_translation(henceforth)
prove([], image)  # → False
prove(frame_axioms(henceforth, "K"), image)  # → True
```

### Equality is not an ordinary atom here

The propositional translation reads an atom as a world-relative proposition. Appending the world to `=` would make identity a world-varying, uninterpreted relation under which `a = a` is not valid, so the translation refuses an equality atom instead of approximating it. The quantified modal logic of {doc}`quantified-modal` is where identity is rigid:

```python
from textwrap import fill

equality = m.parse("a = a")
try:
    FOL(MODAL(equality))
except NotImplementedError as exc:
    print(fill(str(exc), 88))
# → standard_translation: the equality atom 'a = a' ('=') is refused by name — equality is
# → not interpreted by the propositional standard translation. It has no term semantics (an
# → atom becomes a predicate with the world appended, so '=' would become a world-varying
# → uninterpreted relation), so it would read the identity as an uninterpreted proposition
# → and answer wrongly, e.g. 'a = a' false. Use unicode_fol_kit.fol.qml (quantified modal
# → logic, where '=' is rigid identity over the object domain) for a formula with identity.
api.prove(FOL(QML(equality))).status  # → 'proved'
```

The propositional Kripke evaluator refuses `=` and `≠` the same way, for the same reason: it has no semantics of terms.

## Knowledge bases

The two `alc` edges translate a **concept**, read against the empty knowledge base. A TBox with a role box, or an ABox, is a different object, and `dl.kb_to_fol` is its entry point. It follows the same convention as the rest of the graph: the knowledge base comes back as one formula and the role-box axioms **separately**, as premises.

The edge declares `faithful` with no axioms, and that is true of a concept without a data layer. A concept with a data restriction is the one it refuses: the image of `∃hasAge.xsd:integer ⊓ ∀hasAge.xsd:string` is a *one-sorted* formula that a data value satisfies, so closed existentially it is satisfiable, where OWL 2 makes it unsatisfiable (the two datatypes are disjoint) — the sorts, the typing and the datatype lattice that say so are side axioms of a knowledge base, not of one concept. So the edge raises, and the knowledge-base route answers:

```python
from textwrap import fill
from unicode_fol_kit import dl

clash = dl.And(dl.DataExists("hasAge", dl.Datatype("xsd:integer")),
               dl.DataForAll("hasAge", dl.Datatype("xsd:string")))
try:
    api.translate(clash, "alc", "fol")
except dl.UnsupportedDatatypeError as exc:
    print(fill(str(exc).split(". ")[0], 88))
# → alc→fol (dl.concept_to_fol): the concept ∃hasAge.xsd:integer ⊓ ∀hasAge.xsd:string has a
# → data restriction (the data property 'hasAge', the datatype 'xsd:integer', the datatype
# → 'xsd:string')
kb = dl.kb_to_fol(dl.TBox(), query=[clash])
api.prove(kb.unsatisfiability_goal(clash), kb.tbox_premises, timeout=30000).status  # → 'proved'
```

`query=` hands the concepts you are going to ask about to the knowledge base, so the axioms cover them, and `kb.unsatisfiability_goal`, `kb.subsumption_goal` and `kb.instance_goal` build the matching goal. With a data layer the image is sound and not complete: `proved` transfers to OWL 2, `refuted` does not (`kb.refutation_is_decisive`). The data layer has its own section in {doc}`description-logic`.

A `TBox` holds both the concept inclusions and the role box, but `tbox_to_fol` renders the concept inclusions only. Using its output as the knowledge base asks a weaker theory — the GCIs hold, but the roles are unrelated and none is transitive — and it can report a false counterexample for a subsumption the tableau accepts. So `tbox_to_fol` raises `RoleBoxOmittedError` for a TBox that has a role box, unless you write `concept_inclusions_only=True`.

```python
from textwrap import fill
from unicode_fol_kit import dl

tbox = dl.TBox().add_role_inclusion("hasChild", "hasDescendant")
child, descendant = dl.parse_concept("∃hasChild.⊤"), dl.parse_concept("∃hasDescendant.⊤")
dl.subsumes(child, descendant, tbox)  # → True
try:
    dl.tbox_to_fol(tbox)
except dl.RoleBoxOmittedError as exc:
    print(fill(str(exc), 88))
# → tbox_to_fol: this TBox carries side axioms (1 SubObjectPropertyOf axiom(s)) that
# → tbox_to_fol does not render, so its output alone is a WEAKER theory than the TBox and
# → can be refuted where dl.subsumes(…, tbox) succeeds. Use kb_to_fol(tbox, abox) (the
# → knowledge base and the side axioms, to be passed as premises) or, for one box alone,
# → rbox_to_fol(tbox) for the role-box image; pass concept_inclusions_only=True if the
# → concept-inclusion image alone is really what you want.
goal = dl.subsumption_to_fol(child, descendant)
api.prove(goal, [dl.tbox_to_fol(tbox, concept_inclusions_only=True)]).status  # → 'refuted'
kb = dl.kb_to_fol(tbox)
[a.to_unicode_str() for a in kb.axioms]  # → ['∀x ∀y (hasChild(x, y) → hasDescendant(x, y))']
api.prove(goal, kb.tbox_premises).status  # → 'proved'
```

The first `prove` is the false counterexample: the role box was dropped. `kb.tbox_premises` is the TBox image plus the role-box axioms, the right premises for a question about concepts (subsumption, concept satisfiability), and `kb.premises` adds the ABox for a question about individuals. The agreement with the tableau holds on the fragment the tableau decides:

```python
abox = dl.ABox().assert_concept("alice", dl.parse_concept("∃hasChild.Person"))
kb = dl.kb_to_fol(tbox, abox)
entailed = dl.parse_concept("∃hasDescendant.Person")
asked = dl.abox_to_fol(dl.ABox().assert_concept("alice", entailed))
(api.prove(asked, kb.premises).status, dl.instance_check(abox, "alice", entailed, tbox))  # → ('proved', True)
(api.prove(Not(kb.formula), kb.axioms).status, dl.abox_consistent(abox, tbox))  # → ('refuted', True)
```

The last line asks whether the knowledge base is inconsistent: `proved` would mean yes, and `refuted` means it is consistent, which is what `dl.abox_consistent` reports. {doc}`description-logic` has the rest of the description-logic API.

## Where to go next

- {doc}`classical-reasoning` for the many-sorted conventions behind `MSFOL`.
- {doc}`modal`, {doc}`quantified-modal` and {doc}`hybrid` for the semantics the modal edges translate.
- {doc}`transforms` for `to_fol()` on its own, the sort relativisation the `msfol` edge uses.
- {doc}`interoperability` for the HETS edges that join the registry at run time.
- {doc}`mcp` for the `translate` tool, which returns the axioms next to the formula.
