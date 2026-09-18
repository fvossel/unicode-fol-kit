# Changelog

All notable changes to this project are documented in this file. The format is
loosely based on [Keep a Changelog](https://keepachangelog.com/). Versioning is
semantic, but the project is pre-1.0 (alpha): a **minor** release may contain
breaking changes.

## [Unreleased]

## [0.28.0] - 2026-09-18

### `fol.signature`, `fol.subsort_axioms`, `semantics.modelfinder`, CASL — a subsort relation, subset-semantics only

Signature gains subsorts: Mapping[str, FrozenSet[str]] (child sort -> its direct declared parent sorts) and is_subsort(s, t) (the reflexive-transitive closure, computed and cycle-checked in __post_init__ -- a cycle raises ValueError naming it). This is deliberately narrower than full CASL order-sorted algebra: the semantics is the plain subset reading S < T iff ext(S) subset-or-equal ext(T) -- no injection/coercion functions, no casts, no operation/predicate overloading across the hierarchy. Four routes given a Signature with subsorts now honour it identically, checked by differential testing against each other (tests/test_subsorts.py): Signature.validate's declared-vs-actual argument sort checks accept a subsort substitution one-directionally; the new fol.subsort_axioms(signature) returns one direct-edge implication ∀x (S(x) → T(x)) per declared edge, to be added as extra premises under exactly nonempty_sort_axioms's contract — api.prove(goal, [*premises, *subsort_axioms(sig)]) is the one-call validity route; semantics.modelfinder.find_model/find_countermodel/is_satisfiable_finite/is_valid_finite take an optional subsorts= and filter the sorted search using the full TRANSITIVE closure of declared edges against whichever sorts the theory actually uses (not just direct edges -- the model finder's own signature scan only gives a sort a universe when a formula uses it, so a naive direct-edges-only filter would miss a consequence through an unmentioned intermediate sort, caught by this feature's own differential testing before it shipped); and CASL import/export complete the round trip via 'sort S < T' parsing and a subsorts= export argument, while still refusing partial functions, free/generated types, and cross-hierarchy overloading. Omitting subsorts everywhere reproduces prior behaviour byte-for-byte.

The axioms are deliberately NOT folded into to_fol's own output, as a first version of this item did (to_fol(node, signature=sig) conjoined them onto the result). That is a trap for any validity check: api.prove(to_fol(f, signature=sig)) then has to prove the axiom itself, which is not valid, so (∀x:Animal P(x)) → ∀y:Human P(y) came back REFUTED under Human < Animal. Caught in verification before release; the parameter is gone, and a test pins the premise route against the model finder on eight hand-worked cases, including a chain through an unmentioned intermediate sort.

### `hol.ho_modal` — the third-order shallow embedding carries the whole non-counterfactual modal family, and an actualist domain regime

`hol.ho_modal` used to embed only alethic `□`/`◇` at third order, refusing `K_a`, `Ⓞ`, `Ⓖ`, nominals and every other family the parser's third-order-modal grammar already accepted, by name. Both exporters (`isabelle_ho_modal_theory` / `to_thf_ho_modal`) now carry the same non-counterfactual family `hol.thf_modal` / `hol.isabelle_modal` carry at first order, ported rather than reinvented: agent-indexed epistemic/doxastic/assertive/bouletic (`K_a`/`B_a`/`Say_a`/`Want_a`, a new optional `systems=` dict constraining one or more of the four relations, e.g. `{"epistemic": "S5"}`), deontic `Ⓞ`/`Ⓟ` (a serial relation, Standard Deontic Logic), the full temporal family `Ⓖ`/`Ⓕ`/`Ⓝ`/`Ⓤ`/`⒮` and their past mirrors `⒣`/`⒫`/`⒴` (strong Until/Since as genuine `inductive` least fixpoints, not abbreviations, exactly mirroring `hol.isabelle_modal`'s own `muntil`; a one-step relation linked into the henceforth relation by an `Rn_in_Rt`/`tnext_in_t` inclusion axiom, so `Always(P) → Next(P)` stays a theorem of the embedded theory the way it is of `satisfies_modal`), and hybrid nominals/`@` (world constants). The Lewis counterfactuals `Would`/`Might` and the group-epistemic operators `EverybodyKnows`/`DistributedKnowledge`/`CommonKnowledge` stay refused by name, on both exporters — the former reads a similarity ordering rather than an accessibility relation, the latter would need a transitive closure this port does not attempt.

A new `mode=` parameter (default `"constant"`/possibilist, unchanged) adds the actualist domain regime `hol.isabelle_modal` already has at first order — `"varying"`/`"increasing"`/`"cumulative"`/`"decreasing"`, `existsAt`-guarding individual quantification (the latter two share one axiom set, pinned as byte-for-byte synonyms on both exporters — verified by a dedicated structural synonymy test, `test_increasing_and_cumulative_are_synonyms`, over both the Isabelle and THF exporters). The one genuinely new judgment call this port makes, since first order has no property quantifier to decide about: the guard applies ONLY to an individual `Quantifier`, never to a `SecondOrderQuantifier` (property) binder, which stays `mall`/`mex`, constant across worlds, in every mode — live-verified with the classic Barcan formula and its converse (against the first-order embedding's own `qml_is_valid` as an independent oracle, across all four domain regimes) diverging exactly where the individual-level formula does and staying provable at the property level regardless of mode. Every default (mode omitted, no `systems=`) renders byte-identical to the pre-widening module, so `hol.goedel` and this guide's own worked example are unaffected. Caught while writing the live battery: the ported per-agent "euclidean" frame-condition schema had dropped the agent argument from its conclusion, a real Isabelle type clash the moment two agent-indexed systems (e.g. `systems={"epistemic": "S5", "doxastic": "KD45"}`) were declared together — fixed and pinned by a regression test on both exporters. The group-epistemic refusal (`EverybodyKnows`/`DistributedKnowledge`/`CommonKnowledge`, by name) is now pinned on BOTH exporters, not just the Isabelle route — `to_thf_ho_modal` raises the identical `UnsupportedHigherOrderNode`.

### `prob.distribution` / `prob._bdd` — a second, compiled evaluation route: exact weighted model counting via BDDs

`query`'s original route sums `2^k` total choices over the `k` probabilistic facts a goal's dependency cone reaches — exact, but exponential in that count regardless of how much structure the program shares. `query` now takes a `method` keyword: `"enumerate"` (the default, byte-for-byte the original algorithm) or `"compile"` — a second, algorithmically distinct but semantically IDENTICAL route built on a new in-house Reduced Ordered BDD engine, `prob._bdd.BDDManager`. Instead of materialising a total choice, `"compile"` reuses the exact same grounding/pruning/least-model machinery but replaces the Boolean least fixpoint with a BDD-valued one: each derived ground atom gets a canonical Boolean function of the relevant facts, built by the same monotone-lattice fixpoint iteration the enumeration route already uses, and the goal is composed over these functions with identical ∧/∨/¬ structure. The single resulting root is weighted-model-counted bottom-up, so a program whose derivations share a lot of structure (a chain, a tree, a diamond) collapses to `O(#BDD nodes)` instead of `O(2^k)` — the worked example in `docs/guide/probabilistic.md` answers a 20-independent-fact chain (`1/2**20`) that `method="enumerate"` refuses outright past its own `max_choice_facts` brake. Both routes are held to agreeing EXACTLY (`Fraction` equality, never a tolerance) on every program either can answer — the specification this module holds itself to, and what its differential test suite checks directly. `method="compile"` is bounded by its own brake, `max_bdd_nodes` (100 000 by default; `max_choice_facts` does not apply to it), since weighted model counting is `#P`-hard and no fixed variable order escapes exponential ROBDDs in the worst case — this path refuses loudly (`ValueError`) rather than silently grinding, exactly like every other bounded search in the kit.

An adversarial review pass caught and fixed two issues before this shipped. `BDDManager.node()` now raises `ValueError` when asked for a terminal id (`FALSE`/`TRUE`) instead of silently returning an unrelated internal node's tuple via a negative list index — the method's own docstring already promised "never a terminal", and this makes the promise true rather than aspirational; both existing call sites were confirmed to never hit the bad path, so no `query` answer changes. And the module's own seeded random-battery tests were reseeded from `random.Random(f"{shape}-{seed}-{n}")` instead of Python's built-in `hash(shape)`, which is randomized per run by `PYTHONHASHSEED` (unpinned anywhere in this repo) and so silently drew a different sequence on every interpreter invocation — confirmed to differ across `PYTHONHASHSEED` values before the fix, and stable after it.

### `atp.tstp_check` — an independent checker for Vampire/E derivations, tiered honestly

`atp.tstp.parse_tstp_derivation` turns Vampire's or E's printed TSTP proof into a derivation DAG, but nothing re-derived it — the DAG was trusted verbatim. `atp.tstp_check.check_tstp_derivation(derivation, premises, conclusion)` is that independent check, in the same spirit as `atp.resolution_check` and `atp.twee_check`, but TIERED rather than uniform, because a real captured proof mixes three very different kinds of step and pretending they are all equally certifiable would be dishonest. Core rules — binary resolution, factoring, superposition/paramodulation, equality resolution, forward/backward demodulation, and forward/backward subsumption resolution — are independently RE-DERIVED against the stated parent clauses, reusing `atp.resolution_check`'s unification/matching primitives directly rather than trusting the searcher; the equality rules and subsumption resolution needed genuinely new bounded-search checkers, since TSTP carries none of the extra fields a hand-built `ResolutionStep` does. Clausification/normalisation steps (CNF conversion, NNF, flattening, E's `fof_nnf`/`split_conjunct`, and friends) are not re-derived transformation by transformation — any sound clausifier output passes — but each one's stated formula must be ENTAILED by its already-verified parents, which Z3 has to prove within a per-step budget (a timeout is a failure, never a pass). That is exactly what a refutation needs: every statement is then a consequence of the premises plus the negated conjecture. The conjecture itself may be cited only by `negated_conjecture`/`assume_negation`, whose formula must follow from the conjecture's negation; any other step citing it is refused, since entailment alone would let a proof assume what it is proving. Leaves must be alpha-variants of the caller's own premises or conclusion, so no extra axiom slips in that way either. Skolemization is recognised but refused by name: a Skolemized formula is only equisatisfiable with its parent, not a consequence of it, so no entailment check can license it, and a derivation that Skolemizes comes back unverified. Everything outside both tables — AVATAR splitting, global subsumption, an unrecognised or future rule name — makes that step, and therefore the whole derivation, come back unverified, naming the offending rule; never silently accepted.

A soundness bug was caught and fixed by adversarial review before this shipped: forward/backward subsumption resolution matched the subsumer clause's other literals against the FULL target clause, including the very literal about to be dropped, instead of the target minus that literal — letting a tautologous or self-redundant subsumer license dropping an arbitrary target literal it never actually licensed. `{¬p(x)∨p(x), p(a)∨r(b)}` does not entail `r(b)`, yet the buggy checker reported that exact derivation `verified=True`; fixed by restricting the match pool to the target clause with the licensed literal excluded (`C·σ ⊆ D\{M}`, the correct subsumption-resolution condition), re-verified against the same counterexample (now `verified=False`, naming `subsumption_resolution`), and pinned by two new regression tests — the counterexample itself, and a genuine multi-literal-subsumer accept exercising the same code path correctly.

A second, worse hole was found by hand after review: the clausification tier originally only walked each step's parent chain back to genuine leaves and never looked at the step's OWN formula. One `cnf_transformation` step could therefore state anything its author liked — `p(a) ⊢ p(b)` came back `verified=True` from a six-line fake proof whose only lie was `~p(a)` "clausified" out of `~p(b)` — and a step could cite the conjecture positively, certifying `{q(a)} ⊢ p(b)`. Both are closed by the entailment check and the conjecture rule described above, and each fake proof, plus a `negated_conjecture` step that negates the wrong atom, is pinned as a regression test next to a genuine clausification that still verifies. The real Vampire fixtures verify exactly as before.

### `fol.prolog_export` — the missing return leg: kit formulas out as Prolog clauses

`fol.prolog_input.parse_prolog_clause` reads a fact or a definite/normal Prolog clause into a kit formula; `fol.prolog_export.formula_to_prolog_clause` goes back the other way, for a formula that was BUILT to look like one — a rule mined from a structure, a hand-written class definition, or a formula that came from somewhere else and needs to travel back out as text a Prolog engine (or a rule learner such as Popper) can consume. It is deliberately not a general `Node.to_prolog()` method: Prolog can only express a narrow shape (a fact, or a single-headed implication whose body combines facts with `,`/`;`/opt-in `\+`), so most formulas have no Prolog reading at all, and the accepted fragment is the EXACT syntactic mirror of `parse_prolog_clause`'s own `mode="clause"` reading — a bare or `∀`-closed atom, or a `∀`-prefixed `Implies(body, head)` where `head` is a single atom and `body` is built only from `And`/`Or`/`Atom`/`Not(Atom)`. Everything else — a disjunctive head, a variable that occurs only in the head, a nested quantifier, anything outside classical FOL — is refused by name rather than approximated. Every variable is renamed to a fresh `V0`, `V1`, ... in the same alphabetical order `parse_prolog_clause` itself closes them in, so reading the rendered text back lands on the identical quantifier nesting. `negation_as_failure="classical"` mirrors the importer's own opt-in, and the same warning applies in reverse: it makes the round trip syntactically faithful, but `\+ G` still only agrees with `¬G` when the Prolog program is complete for `G`. `formula_to_prolog_program` renders several clauses at once, splitting a top-level `∧` the way `parse_prolog_program` reads several clauses back separately rather than disjoined, and now names which clause failed (position and text) when one formula in the middle of a multi-clause program falls outside the fragment, mirroring `parse_prolog_program`'s own `"(in clause: ...)"` convention on the importing side.

### `atp.incremental` — a persistent Z3 session for repeated same-premise entailment queries

`atp.z3_models` and `Z3Backend` each build a brand-new `z3.Solver` per call — correct, but wasteful against the common "many goals, one premise set" workload (`eval.datasets.fracas`/`prontoqa`/`proverqa`'s paired verdict/negated `api.prove()` calls, `eval.datasets.proofwriter`'s `atom_oracle` loop — all decide many different goals against an unchanged premise list). The new `IncrementalSession` (`unicode_fol_kit.atp.incremental`) keeps one persistent solver alive instead and uses Z3's native push/pop scope stack: `assert_premise` grows the premise set on its own new scope, `retract` undoes the MOST RECENTLY asserted one and returns it (LIFO only — Z3 scopes are a stack, so an arbitrary earlier premise can never be retracted while keeping the rest; that would need Z3's assumption-literal pattern instead, out of scope here), and `decide(goal)` answers any number of goals against whatever the live premise set is, leaving the solver's scope depth exactly as it was before the call regardless of which of PROVED/REFUTED/UNKNOWN it returns. Every verdict is tagged `backend="z3-incremental"`, distinct from the stateless `"z3"` name, so a cache or log never conflates the two even though both decide through Z3. Many-sorted soundness carries over unchanged: `decide` recomputes `fol.nonempty_sort_axioms` for the goal and the CURRENT premise set on every call and asserts it inside that call's own transient scope, so a session never disagrees with `Z3Backend`/`is_valid` on a sorted query — including `(∀x:S φ) → ∃x:S φ)`. This is a standalone utility, not a `ProverBackend` and not reachable through `api.prove`'s backend chain — wiring the dataset call sites above to use it when their resolved chain is Z3-only is a reasonable, separate follow-up.

### `semantics.asp_models` / `semantics.team_translation` — second-order model checking through ASP, and dependence logic's fast path

`satisfies_so`/`holds` are brute force by construction: every `∀P`/`∃P` materialises the full `2 ** (n ** k)` relation powerset in Python, capped by `MAX_RELATIONS`. `semantics.asp_models.asp_holds_so(sentence, structure)` checks the same semantics through clingo instead — an answer-set solver's own choice-and-propagate search replaces the Python enumeration, clearing that cap entirely — but only for a sentence whose `SecondOrderQuantifier` occurrences form a single, contiguous, SAME-polarity block (not necessarily at the sentence's outermost node: `circumscription_entails_so`'s own `∀`-block sits inside an `Implies`/`And`). The encoding is two steps, not one whole-sentence solve: the block's own body is ASP-encoded and solved in isolation against a partly-pinned signature (SAT for an `∃`-block, UNSAT-of-the-negation for a `∀`-block — exactly `asp_find_model`'s own SAT-checking shape), and that single Boolean is spliced back into the surrounding sentence as a fresh 0-ary atom before handing the result to `semantics.tarski.satisfies`, the real recursive evaluator — never a single solve over the whole sentence with the block's wrapper merely stripped, which is unsound the moment the block sits somewhere sign matters (caught by this module's own differential tests against `satisfies_so` before it shipped: a hand-checked `Implies(∀P(P(a)→Q(a)), Q(a))` example disagreed under the naive one-step design). `holds`, and every function built on it (`so_find_model`, `so_find_countermodel`, `so_is_satisfiable_finite`, `so_is_valid_finite`), take an opt-in `fast=True` that switches to `asp_holds_so` for exactly this reason: the default (`fast=False`) is unchanged, and `fast=True` raises `ValueError` — never a silent, possibly wrong, fallback — the moment a formula leaves the single-block fragment. `nonmonotonic.circumscription_entails_so`'s `∀`-block and `team_translation.dependence_to_eso`'s `∃`-block both opt in via the new `team_translation.dependence_holds_eso(sentence, structure, fast=True)`, since both producers only ever emit a single same-polarity block by construction, so `fast=True` never raises for them specifically. Needs `pip install unicode-fol-kit[asp]` (`clingo`), the same optional dependency `asp_find_model`/`asp_minimal_models` already use.

A docstring-accuracy issue was caught and fixed by adversarial review: `_AspEncoder.emit_fixed_facts`'s and `asp_holds_so`'s own `Raises` clauses both claimed a declared predicate with no interpretation in the given `Structure` raises `ValueError`, but the code actually falls through silently to the empty relation for a predicate — matching `tarski._atom_value`'s own documented fallback ("a missing extension is the empty relation, hence false") — and only a missing constant/function interpretation, or a pinned value outside the structure's domain, genuinely raises. The runtime behaviour was always correct; only the docstrings were wrong, and both are now rewritten to state precisely what raises and to note explicitly that a predicate never raises for a missing interpretation.

### `mcp.server` — description-logic reasoning reaches the MCP layer

The ALCHQ tableau and OWL Manchester Syntax bridge (`unicode_fol_kit.dl`) were fully implemented and hand-tested but reachable only from Python — the MCP layer registered zero DL tools. Eight `dl_*` tools close that gap, wiring the existing reasoner with no new reasoning logic of its own: `dl_concept_satisfiable`, `dl_subsumes`, `dl_equivalent`, `dl_abox_consistent`, `dl_instance_check`, `dl_instance_retrieval` and `dl_classify` cover concept satisfiability, subsumption, ABox consistency, the instance/realization family and TBox classification; `dl_parse_manchester` reads a Manchester-syntax class expression, subsumption/equivalence axiom, or role axiom and reports the kit's unicode rendering alongside a `to_manchester` round-trip. Every tool takes concept TEXT under a `syntax` argument — the ALC glyph grammar (`dl.parse_concept`, the default) or OWL 2 Manchester Syntax (`dl.parse_manchester`) — validated up front on every call, even one whose TBox/ABox rows are empty, so a bad `syntax` value is always refused rather than silently accepted; and a TBox/ABox as plain JSON rows rather than Python objects: `{"sub":...,"sup":...}` / `{"equiv":[...]}` for concept-level GCIs, `{"subrole":...,"suprole":...}` / `{"transitive":...}` for the RBox (role hierarchies and transitive roles), and `concepts`/`roles`/`distinct` for the ABox — matching the chemistry tools' own JSON-only, TBox/ABox-as-data convention. Errors follow the same two shapes every other tool in the file already uses: a malformed concept/Manchester text — including a real Manchester construct outside ALCHQ (value/Self/inverse/nominals), which `dl.owl_manchester` already rejects by name — comes back the uniform `ok=False`/`argument`/`errors`/`spec_topic` shape, while a reasoning-level refusal (`NonSimpleRoleError` for a qualified number restriction on a non-simple role, or the tableau's own step-budget `RuntimeError`) is a structured `{"error": {...}}`, since the text itself parsed fine. `mcp.syntax_spec` gains a ninth topic, `description-logic`: the concept-constructor table (glyph and Manchester keyword side by side), the RBox/GCI axiom shapes, and the exact TBox/ABox JSON row shapes the new tools expect — with its own example list (`DL_EXAMPLES`), verified directly against `dl.parse_concept`/`dl.parse_manchester` rather than through `api.parse_any`, which cannot read either grammar.

Every `syntax` argument is validated unconditionally, even on the two tools — `dl_classify` and `dl_abox_consistent` — whose TBox/ABox row-building loop never runs on an empty input: both previously fell through to an `ok=True` result with an invalid `syntax` value silently accepted, since validation had only ever happened as a side effect of parsing concept text that, on an empty call, was never reached. A shared `_check_dl_syntax(syntax)` helper now runs unconditionally at the top of both tools, before their row-building loops, closing that gap; every other `dl_*` tool always parses a required concept-text argument first and was unaffected.

### `dl.owl_functional` — the other OWL bridge: Functional-Style Syntax, whole ontology documents

`unicode_fol_kit.dl.owl_manchester` reads and writes one class expression or axiom at a time; `dl.owl_functional` reads and writes a whole ontology *document* in the W3C's [OWL 2 Functional-Style Syntax](https://www.w3.org/TR/owl2-syntax/#Functional-Style_Syntax), restricted to the same ALCHQ fragment. `dl.parse_owl_functional(text)` reads a `Prefix(...)`-then-`Ontology(...)` document into a `(TBox, ABox)` pair and `dl.to_owl_functional(tbox, abox)` writes one back; `dl.parse_owl_functional_class_expression`/`dl.to_owl_functional_class_expression` do the same for a single class expression, the Functional-Syntax analogue of `parse_manchester`/`to_manchester`. Unlike Manchester's keyword-infix grammar, Functional Syntax is a flat `Keyword(arg arg ...)` S-expression, so rendering has no precedence to resolve — every compound is already fully parenthesised by its own keyword, and every n-ary writer form (`ObjectIntersectionOf`, `EquivalentClasses`, …) is always emitted in the module's own canonical binary/pairwise shape rather than the n-ary grammar shorthand a reader must also accept. `Declaration(...)`, `Prefix(...)`, the ontology/version IRIs, and both axiom-level and standalone `Annotation(...)` are parsed and discarded as the W3C spec itself defines them: non-restrictive. Everything outside ALCHQ — inverse roles, nominals (`ObjectOneOf`), `ObjectHasValue`/`ObjectHasSelf`, every `Data*` construct, property chains, same-individual merging, the other object-property characteristics, `HasKey`, anonymous individuals — is rejected by name through one `OwlFunctionalSyntaxError` per construct, mirroring `owl_manchester`'s own "refuse loudly, name the construct" convention rather than approximating. `ObjectMinCardinality`/`ObjectMaxCardinality`/`ObjectExactCardinality` accept both the unqualified 2-argument and qualified 3-argument spellings the W3C grammar allows (the qualifying class defaults to `owl:Thing` when omitted) and are checked on both the reading and the writing side for both restriction kinds, not just `AtLeast`. As with Manchester Syntax, a name is taken verbatim with no escaping mechanism: round-tripping is only guaranteed for names free of whitespace or structural characters, and a name that violates that renders unescaped but fails loudly at re-parse (`OwlFunctionalSyntaxError` naming the trailing input) rather than corrupting silently — now itself pinned by a regression test, and documented explicitly in the module's own docstring rather than left as a Manchester-only aside. Unlike `dl.to_manchester`, `dl.to_owl_functional`/`dl.to_owl_functional_class_expression` do NOT get an export-only exception for inverse roles or nominals: both are refused in every direction (parse and render alike), with a `TypeError` naming the exact offending construct — there is no OWL 2 Functional-Style Syntax round-trip for either in this kit, matching that format's already-existing parse-side `ObjectInverseOf`/`ObjectOneOf` rejection.

### `dl.owl_reasoner` — an external OWL 2 DL reasoner, for the two constructs the in-house tableau refuses

`dl.tableau` decides ALCHQ(+S) and refuses `InverseRole` and `Nominal` **by name**: inverse roles break its subset-blocking termination argument and nominals need an individual-merging machinery it does not have. That refusal stays exactly as it is — the boundary this kit draws is "detect and refuse, loudly", never "approximate with a homegrown algorithm". `dl.owl_reasoner` adds the other half: the same `TBox`/`ABox`/`Concept` AST is handed to [HermiT](http://www.hermit-reasoner.com/) through [owlready2](https://owlready2.readthedocs.io), an OWL-2-DL-complete mainstream reasoner, so the full fragment — ALCHQ plus I and O — becomes decidable through the kit without the kit pretending to decide it. Ten functions mirror every `dl.tableau` entry point under an `external_` prefix: `external_concept_satisfiable` / `external_concept_unsatisfiable`, `external_subsumes`, `external_equivalent`, `external_abox_consistent`, `external_instance_check`, `external_instance_retrieval`, `external_realize` / `external_realize_all`, plus `available()` and `OwlReasonerError`.

Two things make this an oracle rather than a second opinion. On the fragment the in-house tableau *does* decide, the two must agree **exactly** — satisfiability, subsumption and instance checks, including role hierarchies, transitivity and qualified number restrictions — which is a live differential test, not an assumption. And availability is pure discovery: `available()` uses `importlib.util.find_spec`, never an import, matching `Cvc5Backend.available`'s convention, so probing costs nothing; every public function checks it and raises `OwlReasonerError` naming what is missing rather than silently degrading. A JVM must be on `PATH` for HermiT; a failed JVM launch is re-raised as the same error, never swallowed.

Installed with the new `owl` extra (`pip install unicode-fol-kit[owl]`) and exercised by tests marked `owl_live`, which skip themselves when owlready2 or Java is absent. Worth stating plainly: **owlready2 is LGPL-3.0-or-later**, the first copyleft optional dependency this MIT-licensed kit names. It is an optional, separately installed package the kit only imports — never vendored, never statically linked — but if that licence matters for your deployment, this is the extra to leave uninstalled; nothing else in the kit changes when you do.

### Many-sorted soundness: every classical route now assumes non-empty sorts

`(∀x:S φ) → (∃x:S φ)` reads as an obvious tautology, but nothing proved it: `SortedQuantifier`/`SortedConstant`/`SortedCount`'s reduction to classical FOL (`fol.nodes.to_fol`) relativises a sort to a guard predicate (`∀x:S φ` → `∀x (S(x) → φ)`, `∃x:S φ` → `∃x (S(x) ∧ φ)`) without asserting the guard's extension is non-empty, so a solver was free to make a sort empty and turn a genuinely valid many-sorted formula invalid — or a genuinely unsatisfiable one satisfiable. `is_valid`, `prove`/`countermodel`, `cvc5`, the TPTP `fof` export, `atp.formulas_are_equivalent` and `eval.equivalence`'s solver level could all return a definitively WRONG verdict this way, disagreeing with `semantics.modelfinder` (which has always enumerated only non-empty sort universes as a sort's legal reading) and with TPTP TF0 (which guarantees it natively).

`fol.nonempty_sort_axioms` — one `∃x (S(x))` sentence per sort mentioned, factored out of `atp.finite_domain.lower_msfol`'s own many-sorted front door, which already built exactly these sentences for the ASP/CP backends — is now added by every affected route as an extra, unconditional, never-negated sentence alongside whatever it is deciding: a premise for validity/entailment, an extra conjunct for satisfiability/model-finding. Never folded inside the per-formula translation itself, which stays polarity-blind exactly as before. An unsorted formula is completely unaffected: the axiom list is empty, so every fixed route's solver/Prover9/TPTP input — and its result — is byte-identical to before this release. The kit's own resolution and tableau calculi do not add the sentences yet; for them this is a completeness gap only (they can miss a many-sorted proof that needs a non-empty sort, never report a false one), pinned by a test.

`Cvc5Backend`'s `Verdict.proof['unsat_core']` on a many-sorted PROVED verdict no longer includes the synthetic non-emptiness axiom alongside the caller's own premises: the premises and the non-emptiness axioms now reach `Cvc5Backend._run` as two separate sequences (mirroring `atp.protocol`'s own `z3_premises`/`z3_nonempty_sort_axioms` split) instead of one pre-concatenated list, so `_run` always knows the exact assertion-index range the synthetic axioms occupy and can exclude any core term that is cvc5-Term-equal to one of them before stringifying the reported core — matching how `Z3Backend`'s own `z3_unsat_core` already excluded it. The one documented corner case this cannot cover: a caller premise syntactically identical to a synthetic axiom is silently absorbed into the excluded background fact rather than double-counted, which cannot turn a PROVED verdict unsound since `unsat_core` is already contractually sound-but-not-necessarily-minimal.

### Opt-in native HOL identity for the classical FOL/THF exporters

`to_thf_fol` / `to_isabelle_fol` (and their many-sorted `to_thf_msfol` / `to_isabelle_msfol` variants) accept a new `native_equality: bool = False` flag. Off, which stays the default, `=` / `≠` render exactly as before — the uninterpreted `feq` / `fneq` predicates this HOL layer has always used, byte-identical output, nothing to migrate. On, `=` / `≠` render as the target format's own built-in identity instead: THF's infix `=` / `!=`, Isabelle's polymorphic `=` / `\<noteq>` — both already genuine, axiom-free HOL identity at every type, including the uninterpreted individual type `$i` / `i`. That buys reflexivity, symmetry, transitivity, and congruence with every declared function and predicate for free, with nothing hand-rolled to get an arity wrong on or forget to relativize under a many-sorted guard; `<` `>` `≤` `≥` stay uninterpreted either way, since neither target format has a built-in counterpart for them. A live Vampire (THF, via WSL) and a live local Isabelle/HOL build both confirm the asymmetry directly on the same congruence goal: it closes under `native_equality=True` and does not close under the default in either prover — the demonstration that a hand-rolled congruence-axiom generator would have been unnecessary machinery duplicating what the target logics already provide.

### `Node`, `TruthTable`, `Structure`, `FiniteStructure` — notebook rich-display hooks

Four classes gain the dunder methods Jupyter/IPython's formatter registry already knows how to call, so a formula, a truth table, or a structure now renders directly instead of the default dataclass repr when it is the last expression in a notebook cell — no new dependency; none of the hooks is exercised through IPython, only called directly, and none imports it. `Node._repr_latex_` wraps the existing `to_latex()` in display-math `$$...$$`, and — since IPython's protocol treats an exception from a `_repr_*_` method as a hard cell failure rather than "try the next formatter" — swallows whatever refusal `to_latex()` raises for a node it cannot render and returns `None` instead, so IPython falls back to the plain `repr()`. `TruthTable._repr_html_` builds an HTML `<table>` straight from the same `atoms`/`rows` data `render()`'s Markdown table already walks, via a newly-shared `_rows_and_glyphs()` helper factored out of `render()` — never round-tripping through a Markdown parser, since none is a dependency of this kit. `Structure._repr_html_` and `FiniteStructure._repr_html_` mirror their existing `__repr__`/`to_dict()` output in HTML form: domain and constants, and — for `Structure` — function/predicate `name/arity` keys only, since an interpretation may be a plain Python callable and it is never invoked; `FiniteStructure` additionally renders the small stored-extension tables `to_dict()` already serialises, with a 0-ary predicate's `{()}`/`{}` extension spelled out as an explicit True/False row rather than the visually-empty table both would otherwise render as under the same caption, and lists `computed` predicates by name only, without calling them. Every value that could hold a user-chosen symbol or individual name is HTML-escaped.

### `semantics.kripke` — `KripkeModel.to_dot()` / `to_svg()` for frame and countermodel visualization

`KripkeModel` gains `to_dot()` and `to_svg()`, a pure-Python Graphviz export mirroring `Node.to_dot()`'s own convention exactly: `to_dot()` returns a `digraph Kripke { ... }` string with one node per world (declared in `repr()` order for determinism) and one edge per `(relation, source, target)` triple, labelled with the relation's own name — the one place a naive per-pair rendering would lose information, since a model can carry several named relations over the same world set at once (two agents' `K:`/`B:` relations, `alethic`, `temporal`, `deontic`, all coexisting), and the label is what keeps them visually distinguishable instead of collapsing into indistinguishable arrows. Every node's label carries the world plus, by default, the atoms `atoms_true_at` returns there, any nominal name(s) pointing at it, and its object domain if the model carries one; world/atom/relation names with spaces, quotes, backslashes or non-ASCII text are escaped for valid DOT syntax. `to_svg(dot_binary=None)` pipes `to_dot()` through the Graphviz `dot` binary (`dot_binary` or `shutil.which("dot")`), raising `RuntimeError` naming the missing tool rather than ever falling back to a partial rendering — the same shutil.which-gate-and-fail-loudly pattern already used for the optional external provers (eprover, minizinc, Vampire, Prover9, Isabelle) elsewhere in this kit. A `_repr_svg_()` hook returns `None` instead of raising under the same missing-Graphviz condition, so a model displays fine (falling back to its plain `__repr__`) in a notebook with or without Graphviz on `PATH`. Both are read-only inspection methods — model construction and `satisfies_modal` are untouched — so `atp.modal_tableau.modal_countermodel`'s and `hol.isabelle_runner.isabelle_decide_modal`'s returned `KripkeModel` instances get the feature for free, with zero adapter code.

### `fol.tptp_input` — `include(...)` directives, and the two annotation fields a TPTP statement can carry

`parse_tptp`, `load_tptp`, `parse_tptp_problem`, `load_tptp_problem`, `parse_tff_problem`, and `load_tff_problem` now resolve `include('path')` / `include('path', [name1, name2])` directives: first relative to the including file's own directory (`base_dir`, set automatically by every `load_*` entry point; bare text left at `base_dir=None` refuses an include by name rather than guessing, so every existing text-only caller — `parse_tptp_formula` included, which never resolves includes at all — is untouched), then each root in `search_paths`, then `os.environ["TPTP"]` if set, matching how external TPTP tooling locates a shared library. A selection list imports only the named formulas, in the order named, and refuses a name absent from the included file; a missing file or a circular include chain (`A` includes `B` includes `A`) is refused, naming the path or the whole chain, never silently dropped or looped — cycle detection is seeded with the loaded file's own path, so a chain that loops back to the very file you started from is caught too. The TF0 (`tff`) reader resolves whole-file includes exactly the same way, splicing type declarations and formulas alike, with one narrow, explicitly named restriction: a selection list cannot be applied to an included file whose own contents still carry a `tff(name, type, ...).` declaration, since that declaration's TPTP statement name is never tracked separately from the symbol it declares — a limitation of the existing TF0 declaration records, not of includes; the whole file (no selection) always works regardless. The same grammar change also lets every `fof`/`cnf`/`tff` statement carry the optional 4th (`source`) and 5th (`useful_info`) annotation fields real TPTP files use for provenance and derivation metadata (`file(...)`, `inference(...)`, ...); they parse and are discarded, so a 3-, 4-, and 5-field statement all produce the identical `TptpFormula`. `fol.tptp_repair.repair_tptp_problem` follows suit: it passes `include(...)` directives through untouched instead of refusing the file, and a statement's annotations are no longer taken for part of its formula — the formula ends at the first comma outside brackets, and the annotations come back verbatim. Every include-resolution test is checked against hand-flattening as an independent second route — an included file's own text, spliced at the include's position and parsed as one document with the pre-existing, include-oblivious `parse_tptp` — plus a dedicated on-disk fixture tree under `tests/fixtures/tptp_include/` pinning the two-tier `base_dir`-then-`search_paths` lookup order against a naive same-directory-only resolver.

### `dl` — instance queries, realization, and TBox classification

Four ABox reasoning tasks join the ALC tableau's public surface:
`dl.instance_check(abox, individual, C, tbox)` decides `individual : C`
entailment the same way `dl.subsumes` decides subsumption — assert the
complement and check for inconsistency, this time one level up at the ABox
rather than the concept layer — `dl.instance_retrieval(abox, C, tbox)`
sweeps it over every named individual, and `dl.realize`/`dl.realize_all`
reduce further to return an individual's (or every individual's)
most-specific types from a caller-supplied vocabulary, filtering to an
antichain by dropping any concept a kept sibling strictly subsumes.
Alongside them, `unicode_fol_kit.dl.classify` turns the pairwise
`dl.subsumes` relation into the aggregate structure an OWL reasoner's
classifier reports: a `Classification` with `equivalents` (mutual-subsumption
synonym classes, keyed by their lexicographically smallest member so output
is deterministic), a transitively-reduced `parents`/`children` Hasse diagram,
and the full `ancestors` closure as a free byproduct of the same O(n²)
matrix. Neither addition introduces a single new tableau completion rule —
both are pure reductions to already-tested primitives (`abox_consistent`,
`subsumes`), so they carry no new soundness or completeness burden, and both
are hand-checked against textbook taxonomies plus differential cross-checks
that re-derive the reduction independently inside the tests rather than
trusting the implementation under test.

### `atp.finite_domain.lower_msfol` — many-sorted input reaches the ASP/CP backends

`ClingoBackend` and `MinizincBackend` now accept many-sorted input directly,
not just classical FOL plus counting. `atp.finite_domain` gains
`lower_msfol`, which both backends' `decide()` call on their refutation-goal
sentences right after building them and before `fragment_check` (or, for
MiniZinc, `Signature.from_formulas`) ever sees them: a `SortedQuantifier`/
`SortedConstant`/`SortedCount`/`SortedCardinality` sentence is relativised to
plain classical FOL with the kit's own `to_fol` — the same pattern
`atp.z3_arith` already uses ahead of its own arithmetic translation — so a
sort name becomes an ordinary unary predicate everywhere downstream, and
`fragment_check`, both encoders, and `verify_model` stay entirely sort-blind;
none of them changed. One soundness point `to_fol`'s relativisation alone
does not cover: a many-sorted logic's sorts are never empty by convention, so
`lower_msfol` also asserts one non-emptiness sentence per distinct sort name
referenced. The lowering is applied per SENTENCE, not per batch: a sentence
with no sorted node of its own — including an unrelated `Count`/`Contrast`
premise sharing a `decide()` call with a sorted sentence — is left completely
untouched, so it keeps its backend's own native counting encoding and is
never at risk of `to_fol`'s bounded `Count`-expansion step. A sentence batch
with no sorted node anywhere passes through `lower_msfol` completely
untouched, so every pre-existing unsorted entailment decides exactly as
before.

### `fol.msflparser` — modal/tomodal get LALR speed too, without losing Earley's reach

`modal` and `tomodal` no longer pay the full Earley cost on every formula.
`MSFLParser` now builds BOTH an LALR parser (the fast path) and the Earley
parser it used exclusively before, tries LALR first, and falls back to
Earley — transparently, on any of Lark's three failure exceptions — only on
the input shapes LALR cannot resolve. Measured on the FOLIO corpus in modal
mode: 102 → 1060 formulas/second through `MSFLParser.parse`, a **10.4x**
speedup (best of three runs). 1260 of FOLIO's 1310 lines parse via LALR
alone, and the remaining 50 are rejected by both parsers identically
(genuinely malformed, not fallback-shaped) — the fixture never actually
exercises the fallback's slow path.

The reason `modal` could not just move to plain LALR, as the eight
non-modal modes did in 0.23.2: a genuine LALR(1) reduce/reduce conflict
between `atom_term`'s `"(" term ")"` and the hybrid-logic bare-nominal rule
(`?nominal.-1: (NAME | VARIABLE)`, sharing an LALR state after `"("` plus a
bare lowercase name/variable) that the nominal rule's own `-1` priority —
added for an unrelated lambda-application disambiguation — resolves toward
the wrong reading. `(q→p)`, `(p∧q)`, `(p→p)` all fail outright under plain
LALR while the same shapes headed by an uppercase predicate, e.g. `(P→P)`,
succeed. Lark offers only Earley and LALR(1), and eliminating this cleanly
would need grammar state-splitting with no guaranteed clean answer — exactly
the silent-narrowing risk this project refuses to ship — so Earley stays, as
a fallback rather than as the mode's parser.

Soundness — not just a superset of what LALR accepts, but the SAME tree
wherever it does — is the property that actually matters, and it is the one
a `parser="lalr"` swap cannot get away with asserting from a small sample.
`tests/test_parser_backend.py`'s FOLIO/MALFORMED differential, previously
run only against the eight non-modal modes, now also runs against modal and
tomodal through the real wrapper, with zero mismatches. A new
`tests/test_modal_lalr_fallback.py` adds a seeded random generator of modal
and third-order-modal formulas — every modal/temporal/epistemic/doxastic/
deontic operator, hybrid `@`/nominals, second-order and lambda arguments for
tomodal, parenthesised bare atoms, mixed precedence without parentheses —
3000 formulas per mode: wherever the raw LALR parser accepts, the raw
Earley parser is checked to accept the SAME text and build the IDENTICAL
tree, spot-checked further at the `to_dict()` AST level through the full
`MSFLParser.parse` pipeline, and wherever Earley accepts, the wrapper is
checked to accept too. Zero mismatches, alongside a hand-written adversarial
corpus of 220 bracket-grouped bare-atom shapes beyond the original 8 (bare
`VARIABLE`, bare multi-letter `NAME`, nested parens, `@i(...)` with no
space, every classical and until-level connective) proving the fallback
path is exercised by more than one family of string.

The error model is untouched: a formula both parsers refuse is reported
through Earley's own, untranslated exception — exactly as when Earley was
the only parser — so `NamingError`/`ParsingError` text for modal/tomodal is
byte-identical to before.

### `atp` — which premises did a PROVED entailment actually need?

`Verdict` gains an optional `relevant_premises` field: 0-based indices into
the caller's `premises`, filled only on request and only for a PROVED
result. Like `proof`'s unsat-core certificate, a reported set is SOUND (the
entailment still holds over just that subset) but not guaranteed MINIMAL —
the underlying solver or prover is never asked to find the smallest
sufficient subset, only a sufficient one. Two routes fill it, and
`api.prove` gained a keyword to reach them uniformly.

`atp.protocol.z3_relevant_premises(formula, premises, timeout=…)` runs one
per-call Z3 `Solver` with every premise and the negated goal asserted under
`assert_and_track` (the same call `Z3Backend` itself now uses for its own
`"kind": "z3_unsat_core"` proof certificate, factored into a shared helper so
neither drifts from the other), and reports the tracked premise tags Z3's
own `unsat_core()` kept — never the goal tag itself, which is trivially
"needed" and carries no information about which premises were. `unsat_core`
tracking runs on that one `Solver` instance only, never through
`z3.set_param`, so it cannot change solving behaviour anywhere else in the
kit that shares Z3's default context.

The two SMT backends now also say why they proved something. A PROVED
`Z3Backend` verdict carries `proof = {"kind": "z3_unsat_core", "core": [...]}`,
the tracked assertion names Z3 kept (`p<i>` for premise *i*, `goal` for the
negated goal). A PROVED `Cvc5Backend` verdict carries `{"kind": "cvc5_alethe",
"text": ..., "unsat_core": [...]}`: cvc5's Alethe proof text and its unsat core,
with the kit's original symbol names restored. To make the core name individual
premises, cvc5 now receives each premise as its own `(assert …)` rather than one
folded implication, which is the same problem logically. REFUTED and UNKNOWN
verdicts keep `proof=None`.

`atp.eprover_backend.eprover_relevant_premises` runs E exactly once — through
the same subprocess plumbing `check_entailment_eprover_detailed` already
uses — and, only on a PROVED verdict, walks the resulting TSTP derivation
backward with the new `atp.tstp.relevant_premises_from_tstp`. That walk is
deliberately separate from `TstpStep.parents`: the existing parser drops a
parent-list entry that is itself a compound, unnamed `inference(...)`
sub-step, which is the right choice for a proof-DAG *display* but would
undercount a relevance query, since E nests almost every real inference step
this way. `relevant_premises_from_tstp` instead recurses into those nested
steps down to every reachable `axiom`-role leaf, starting from every step
whose formula is `$false`. Each such step with its ancestors is a derivation
of the contradiction from exactly those leaves, so the reported premises are
sufficient whenever E's PROVED verdict is; several `$false` steps report the
union of their leaves, which is sufficient for the same reason. A text with no
`$false` step is not a refutation, and a derivation that cites a step it never
defines is incomplete: both give `None` rather than a guessed set.

Vampire has no such route. It renames every TPTP statement, axiom leaves
included, to its own `f1`/`f2`/… scheme regardless of the `premise_<i>` names
the kit's problem generator uses (verified live against `vampire --proof
tptp` 5.0.1), so its derivation cannot be mapped back to the caller's premise
indices without an alpha-equivalence matcher the kit does not have.

`api.prove(…, relevant_premises=True)` ties the routes together: on a PROVED
verdict, it re-asks the SAME backend that produced the answer — never a
different backend's independent proof of the same entailment — currently
routed only for `"z3"` and `"eprover"`; any other winning backend, or a
query that route itself could not answer, leaves the field at its default
`None`. Off by default, since it re-runs the winning backend's decision
procedure a second time.

### Native TF0 — typed TPTP as its own dialect, not a guard-predicate encoding

A many-sorted formula exported through `Node.to_tptp` has always gone out flat: `∀x:Human φ` becomes `![X]: (human(X) => φ)`, a plain FOF formula with one extra predicate per sort. `atp.tptp_tff` now writes TPTP's OTHER first-order dialect instead — TF0, monomorphic typed TPTP — where a sort is a genuine `tff(name, type, S: $tType)` declaration and a bound variable is genuinely typed (`![X: human]: …`), not guarded. Sort/argument-position inference is the same union-find `casl_export` already solved for CASL's structurally identical problem, reused here with `$i` (TPTP's own implicit individual type) standing in for CASL's `default_sort`; `fol.tptp_input.parse_tff_problem` reads it back, returning the declared `Signature` alongside the formulas. `vampire_entailment` and `eprover_backend` (E, Zipperposition) auto-select this route the moment a sorted node appears anywhere in a problem (`tff=` overrides it either way). Scope is deliberately narrow: THF, TF1 polymorphism (`!>`, type variables) and TPTP's arithmetic sorts (`$int`/`$rat`/`$real`) are refused BY NAME on both the writer and the reader.

Getting there surfaced a genuine soundness subtlety worth recording rather than hiding: TPTP TF0 quantifiers range over non-empty types (matching this kit's own many-sorted model finder), but the pre-existing guard-predicate `fof` route never asserted that for a sort with no witness constant, so `∀x:S φ ⊢ ∃x:S φ` is a `tff` theorem the classical export can legitimately fail to prove. Verified live against both Vampire and E: the two routes agree on every ordinary sorted entailment, and diverge on exactly that one non-emptiness-dependent shape.

A second, smaller finding from hardening this item's own tests: on the `tff` route, `check_entailment_vampire_detailed`'s and `check_entailment_eprover_detailed`'s `derivation` field is currently always `None`, even for a genuine successful proof — the shared TSTP-derivation scanner in `atp.tstp` only recognises `fof`/`cnf` proof-line statements, not `tff`/`tcf` ones yet. `output_excerpt`/`raw` are unaffected (they carry the full un-reversed prover text regardless). `check_entailment_eprover_detailed` was also adjusted so an empty derivation reports `None` rather than an empty `{'steps': []}`, matching `check_entailment_vampire_detailed`'s existing behaviour exactly.

### `dl` — RBox: role hierarchies and transitive roles (ALCH+S)

`TBox` grows an RBox alongside its GCIs: `add_role_inclusion(sub_role, super_role)` (`r ⊑ s`) and `add_transitive_role(role)` (`Trans(r)`), both chainable like `add`/`add_equivalence`. The tableau's ∀-rule gains exactly two generalisations, confined entirely to `_saturate`: the edge/restriction match widens from `role == c.role` to `role ⊑* c.role` (rule H, role hierarchies — an `r`-edge counts as an `s`-edge for every declared `r ⊑ s`, and a ⊑-cycle simply collapses the roles on it into one semantic equivalence class, checked by a dedicated regression test on both the internal RBox closure and the semantic subsumption flip through the public API), and whenever that match fires across an edge for which some transitive role bridges the edge's own label and the restriction's role, the whole restriction is re-copied onto the successor so it keeps firing along the rest of the chain (rule S, the textbook "forall-plus" rule). Together this is ALCH plus transitive roles — the non-inverse fragment of SH — and the tableau module docstring carries the soundness and termination argument, citing Horrocks and Sattler's 1999 DL'99 paper. `instance_check`/`instance_retrieval`/`realize`/`realize_all`/`classify` all pick up RBox support for free, since every one of them is a pure reduction back to `concept_satisfiable`/`abox_consistent`. `dl.translate` gains `rbox_to_fol(tbox)`, the FOL image of the same two axiom families, checked against the tableau through a randomized Z3 differential battery with zero disagreements. `dl.owl_manchester` reads and writes the two matching one-line RBox spellings, `"r SubPropertyOf s"` and `"r Characteristics: Transitive"`; every other OWL role characteristic is rejected by name.

### `atp.ltl_tableau` — a complete decision procedure for standard linear-time LTL(+Past)

The Always/Eventually/Next/Until operators and their past mirrors Historically/Once/Previous/Since have always been rejected outright by the labelled modal tableau ("no rule — use qml or isabelle") and only ever soundly-but-incompletely decided by `qml_is_valid`'s first-order embedding, because the kit's own Kripke semantics for these operators is a general, not-necessarily-linear accessibility relation — not the standard discrete order (the natural numbers under <=) the LTL literature means by the name. `atp.ltl_tableau` is a NEW, self-contained module that decides exactly that narrower, standard question — the one PSPACE-complete decision problem — via a Fischer-Ladner closure over the eight temporal operators (forward fixpoints unfolded through their own Next-wrapped continuation, backward ones through their own Previous-wrapped continuation, with Once/Since needing the existential "not Previous not" form of that continuation since Previous itself is only ever weak) and a Wolper-style generalized-Buchi emptiness check on the resulting finite tableau graph — including the easy-to-miss fairness obligation an IMPLICIT negation of Always(phi) still carries even though only `Always(phi)` itself is ever a closure element, a subtlety that cost a real bug during development (documented in the module and caught by the equivalence of `Eventually(p)` and the negation of `Always(not p)` before it ever shipped). `ltl_valid`/`ltl_decide`/`ltl_countermodel` mirror `modal_tableau`'s surface; `ltl_countermodel` returns an explicit `LTLTrace` lasso (finite prefix + infinite cycle), verified before release by `ltl_trace_satisfies` — a direct evaluator over the lasso, independent of the closure/graph machinery, mirroring how `modal_countermodel` verifies against `satisfies_modal`. Both `mode="initial"` (the default — validity anchored at position 0, the reading every textbook validity claim about a logic with past operators means) and `mode="floating"` (true at every position of every model — strictly stronger, and where the two diverge: "there is no earlier position" is initial-valid but not floating-valid) are supported. It is a genuine completeness gain over the rest of the kit: temporal induction (`p` and `Always(p implies Next(p))` implies `Always(p)`), which `fol.qml`'s own module docstring names as staying "genuinely out of reach" for the first-order embedding, is proved directly here. Registered as the `"ltl-tableau"` `ProverBackend` — reached by name, like the external provers, never silently joining `default_chain("modal")`, since it decides a strictly narrower frame class than `modal-tableau`/`qml` share (it can never refute what `qml_is_valid` already proved, only prove strictly more).

### `ace.reverse_modal` / `ace.verbalize` — modal/deontic formulas verbalize to ACE text (ACE-7)

The backward ACE pipeline (ACE-6) now covers `Box`/`Diamond`/`Obligatory`/`Permitted`, on top of the untouched classical route: `ace.reverse_modal.fol_to_modal_drs` recognizes exactly the two shapes ACE's modal surface can carry — a modality wrapping a whole formula (`ModalBox`, "John must wait.") and one nested in a duplex's consequent (`ModalImpl`, "Every man must wait.", verbalized as "If there is a man X1 then X1 must wait.") — reusing `drt.reverse.fol_to_drs` (read-only, untouched) for every classical subformula and refusing every other placement with that same route's own message. `ace.verbalize` threads a `modality` parameter through its existing clause renderer: the ACE auxiliary sits inside the verb phrase and forces the bare/infinitive lexicon form, probed live against APE. Because the auxiliary only ever reaches the text through the event-anchored verb clause, a modal box whose single clause instead comes from a bare noun introduction, a predicative constant, an equality or a comparative is refused by name (`AceVerbalizationError`, "single verb clause") rather than silently dropping the modal auxiliary from the generated text — caught and closed before release by an adversarial review of the initial implementation. Two entry points close the ACE-6 pattern: `modal_formula_to_ace(formula)` and the live self-check `modal_ace_round_trip`, judged by `eval.equivalence.equivalent` rather than raw Z3. All 5 recorded modal corpus fixtures round-trip live against the pinned APE commit, Z3/exact-equivalent to their originals. Question and command verbalization stay explicitly deferred.

### `atp.kripke_enum` / `fol.frames` — Löb, Grz and McKinsey get a bounded finite-frame refutation route

The three modal axioms with no first-order frame condition at every cardinality — Löb (`GL`), Grzegorczyk (`Grz`) and McKinsey (`S4.1`) — used to be refused outright by `atp.kripke_enum.modal_enum_search`, on the claim that they are "not properties of a frame's relation at all". That claim was false: on a FINITE, BOUNDED frame each has a purely structural characterisation — irreflexive (Löb, alongside the separately-listed `trans`), antisymmetric (Grz, alongside `refl`/`trans`), and "every world reaches a terminal point" (McKinsey, restricted to preorders — the only generality the registry ever uses it in, via `S4.1`) — and `fol.frames.holds_on_finite_frame` now decides all three directly, so `kripke_enum` refutes formulas over `frame="GL"`/`"S4.1"`/`"Grz"` exactly like it already did for every first-order condition. No public signature changed anywhere. The correspondence is brute-forced, not asserted, against genuine axiom validity via `satisfies_modal` on every frame up to four worlds (`tests/test_modal_frame_registry.py`), including a non-vacuity control confirming refl+trans alone — the OLD, buggy `FRAME_CONDITIONS["grz"].description`, which omitted antisymmetry and was consequently vacuous on any finite frame — is genuinely insufficient for Grz: it disagrees with true validity on exactly 1/10/136 frames at 2/3/4 worlds. That description is now corrected to name antisymmetry as the load-bearing condition. This is a REFUTATION-only capability and does not touch the unrelated, unbounded PROOF direction: every route that instead emits a single first-order sentence over frames of every cardinality — `fol.qml`, `fol.modal_translation`, `atp.fitch` (via `unguarded_frame_axiom`), and the labelled tableau — still refuses these three axioms by name, unchanged; the tableau's refusal message now also points at `atp.kripke_enum` for the bounded route.

### `dl` — qualified number restrictions close the loop: ALCHQ

`dl.AtLeast(n, role, C)` (≥n r.C) and `dl.AtMost(n, role, C)` (≤n r.C) add qualified number restrictions on top of ALC(H+S), giving **ALCHQ**. The tableau gains three genuinely new completion rules alongside the existing ⊓/⊔/∃/∀: a ≥-rule that generates n pairwise-distinct witnesses (mirroring the ∃-rule, but tracking forced distinctness explicitly — this reasoner makes no unique name assumption, and `ABox.assert_distinct` is the new way to force two individuals apart), a genuinely nondeterministic ≤-rule that merges non-forced-distinct role-neighbours when there are more than the bound allows (redirecting every edge, label and distinctness pair from the discarded node onto the survivor, and branching over every candidate pair for completeness), and the choose-rule the ≤-rule needs to be complete. Number restrictions are refused by name on NON-SIMPLE roles — a transitive role, or one with a transitive sub-role — via a new `NonSimpleRoleError`: combining unrestricted transitivity with counting is undecidable (Horrocks, Sattler & Tobies 1999/2000; the same restriction SHQ/SHIQ use), so this is checked once, by name, before the tableau ever starts. Role hierarchies compose correctly with counting — an r-successor counts as an s-neighbour for every declared r ⊑* s, counted once even when reached by more than one entailing edge at once — so ALCQ combines cleanly with the previous release's RBox work; an adversarial review of this item caught (and this release fixes) a branch-corrupting crash in exactly that convergent-edge case, now covered by both hand-checked regression tests and a dedicated randomized differential battery. `dl.owl_manchester` now parses/renders `min`/`max`/`exactly` per the W3C grammar (the qualifying class optional, defaulting to `owl:Thing`; `exactly n C` desugars to `AtLeast(n, C) ⊓ AtMost(n, C)`), and `dl.translate.concept_to_fol`/`abox_to_fol` route the new constructors through the kit's existing counting-quantifier FOL node, `fol.nodes.Count`, reusing its already-tested distinct-witnesses expansion rather than a new encoding — this doubles as the differential oracle several randomized batteries (concepts, ABoxes, and ABoxes with role hierarchies, decided independently by Z3) are checked against with zero disagreements, alongside hand-checked textbook cases (pigeonhole unsatisfiability, forced-merge ABox scenarios, and the role-hierarchy convergent-edge cases the review added). Plain ALC/ALCH+S inputs are entirely unaffected: every new rule is a no-op unless an `AtLeast`/`AtMost` is actually present, and the full pre-existing dl test suite passes unchanged.

### `atp.z3_input.to_smtlib` — a public, sanitisation-correct SMT-LIB2 writer

The read side (`parse_smtlib`/`load_smtlib`) has had a write-side gap since day one: `atp.z3_input` gains `to_smtlib(formula, premises=(), *, logic="ALL")`, and `Node` gains the single-formula convenience method `to_smtlib()` — wired into the CLI (`--to smtlib`) and the MCP `render` tool (`to="smtlib"`) alongside the existing unicode/tptp/prover9/latex/casl/json/english targets. This is deliberately not `Node.to_z3()` + `z3.Solver.to_smt2()` alone, which is demonstrably unsound: a pure-ASCII digit-leading name (`2008SummerOlympics`) prints unquoted and fails Z3's own reparse, and so does an SMT-LIB2 word Z3's own parser treats as syntax (`let` prints as the undecorated head of `(let x)`, which Z3's own parser then reads as the `let`-binding form). Instead the writer promotes `Cvc5Backend`'s already-proven sanitiser (`SmtNameMap`/`_sanitize_many_for_smtlib`) to run over every premise and the goal sharing ONE name map, each emitted as its own `(assert ...)`. The sanitiser's reserved-word set was narrowed during review to the 7 words (`!`, `_`, `as`, `exists`, `forall`, `let`, `match`) that Z3's parser actually treats specially, after live verification showed the other 6 words the SMT-LIB2 grammar formally reserves (`BINARY`, `DECIMAL`, `HEXADECIMAL`, `NUMERAL`, `par`, `STRING`) already round-trip correctly unsanitised — so a name like `par` or `STRING` used as a kit predicate/constant now round-trips through `to_smtlib`/`parse_smtlib` unchanged, instead of being needlessly renamed. Refusal is inherited, not reimplemented: a construct that `to_z3()` itself has no encoding for raises the identical `NotImplementedError`, with one sentence appended pointing at SMT-LIB2 export specifically.

### `hol.ho_modal` — Löb, McKinsey and Grz in the third-order embedding

`isabelle_ho_modal_theory` and `to_thf_ho_modal` accept the frames `GL`, `S4.1` and `Grz`. None of the three has a first-order frame condition, so the embedding states each as the schema itself, over propositions (`sigma` / `mu > $o`), with the schema variable bound explicitly (`∀P::sigma.` / `! [P: mu > $o]`) rather than left free, so a user symbol named `P` cannot stand in for it. Checked live against Isabelle: under `GL` the Löb schema and 4 are provable and T is refuted by Nitpick, under `Grz` the Grz schema, T and 4 are provable, and the frame axioms have a model.

### `atp.leo3_backend` — Leo-III answers are checked against the modal tableau

Every PROVED or REFUTED verdict from `Leo3Backend` is decided a second time by the kit's own `modal-tableau` on the same formula, premises and frame. Leo-III's accepted fragment here (propositional mono-modal K/T/S4/S5) is one the tableau decides completely, so a disagreement in either direction is reported as `ERROR` with `SOUNDNESS ALARM` in `detail`; only the tableau's own resource bound leaves Leo-III's answer standing, marked `inconclusive`. A confirmed REFUTED verdict carries the tableau's verified Kripke countermodel.

### `eval.metric_hf` — `import unicode_fol_kit` no longer imports `evaluate` and `datasets`

The module docstring said only instantiating `FolEquivalence` needs the optional `evaluate` package, but the import ran at module load, and `eval/__init__.py` loads the module for `compute_fol_metrics`, so every `import unicode_fol_kit` paid for `evaluate` and `datasets` when they were installed. Availability is now a `find_spec` check and the class is built on first access through a module `__getattr__`; every documented access path, `isinstance` checks and pickling included, is unchanged. Measured with `python -X importtime` in an environment that has both packages: about 2.6 s before, 0.6–0.7 s after.

### Fixed: a numeral compared with a cardinality could be read as an individual

`semantics.tarski` resolved a `Number` through `structure.constants` before comparing it, also when the other side of `<`, `>`, `≤`, `≥`, `=` or `≠` is a cardinality `|{x : φ}|`. The model finder interprets every numeral it scans as a constant, so it could map the `1` in `|{x : Pass(x)}| > 1` to some other individual and report a countermodel to a valid entailment — two named, distinct passers do entail more than one passer. Next to a cardinality a numeral is now the number it spells; everywhere else it still goes through the constant table.

### Fixed: THF from the third-order exporters did not parse

`hol.thirdorder.to_thf_to` and `hol.ho_modal.to_thf_ho_modal` wrote predicate names verbatim, so `Positive` or `G` became a THF constant with an upper-case initial — a variable in TPTP — and the type declaration `thf(G_type, type, ( G : $i > $o ))` is rejected by a THF parser (verified against Vampire 5.0.1). Axiom names such as Gödel's `A1` had the same problem. Free symbols are now spelled as lower words through the kit's THF naming, renamed apart when two of them would coincide (`Pos` and `pos`) or take one of the embedding's own names (`r`, `mu`, `mbox`, …); bound variable tokens avoid every token already bound further out; axiom names are made unique lower words; and the modal export now declares the comparison relations (`feq` and friends) it uses. Offline tests pin the lexical shape, and live tests parse the output with Vampire and prove small classical third-order goals with it.

### Fixed: a user predicate named like the modal translation's own relation

`fol.qml` translates a modal formula into first-order logic with its own predicates — `World`, `Object`, `E` for existence, `R` for alethic accessibility, `T`/`N`/`D` and `Rk`/`Rb`/`Rs`/`Rw` for the other families — and appends a world argument to every user atom. A user predicate with one of those names therefore BECAME the translation's predicate: a unary `R(alice)` turned into `R(alice, w)`, the accessibility relation itself, so `R(alice) → ◇R(alice)` came out VALID in K although a dead-end world refutes it; with any other arity the clash crashed Z3. Found while re-checking QMLTP-style problems, which use predicates like `r` and `e` all the time. A colliding user name now gets one trailing `·` (U+00B7, punctuation no parser puts into an identifier) — an injective renaming that never produces a reserved name, applied alike to atoms, sort guards and the per-world sort non-emptiness axioms — and every formula that avoids those names translates byte-for-byte as before. `fol.modal_translation`'s propositional standard translation had the same clash for `R`/`T`/`N`/`D` and the agent-indexed `Rk_`/`Rb_`/`Rs_`/`Rw_` names; there it could only crash (without quantifiers an unreachable extra element absorbs the confusion, so no verdict was wrong), and it gets the same renaming. Nine hand-worked verdicts pin the qml route, four the propositional one.

### Fixed: the Isabelle backend refuted `∀x (x = x)`

`api.prove(..., backends=["isabelle"])` decided classical formulas through `isabelle_decide_fol`, whose embedding renders `=` as the uninterpreted predicate `feq`. That is documented FOL *without* identity, but the backend mapped nitpick's countermodels to `REFUTED`, a verdict every other backend reads with identity: `∀x (x = x)` came back REFUTED and the congruence `∀x ∀y ((x = y ∧ P(x)) → P(y))` could never be proved. `isabelle_decide_fol` gains `native_equality` (default `False`, unchanged output), and the backend always passes `True`, refusing an explicit `native_equality=False`. The modal route is unaffected: the Kripke evaluator reads `s = t` as an ordinary atom, exactly like the modal embedding. A live test checks reflexivity and congruence PROVED and `∀x ∀y (x = y)` REFUTED against a local Isabelle, agreeing with Z3.

### `eval.converses` — declared converse/argument-permutation axioms, opt-in

Two predicates can name the same relation with their arguments swapped or permuted — `LovedBy(x, y)` and `Loves(y, x)`, or `Between(a, b, c)` and `BetweenRev(c, b, a)` — a gap neither `exact_match` (never renames a predicate) nor `align_symbols` (renames names but deliberately never touches argument order) closes. `eval.converses` closes it the other way round: the CALLER declares the bridge explicitly, per comparison, as a `(a_key, b_key, permutation)` triple of `(name, arity)` predicate keys. `validate_converses` rejects an arity mismatch, a non-bijective or wrong-length permutation, a predicate declared its own converse, a built-in predicate name, and the same unordered pair declared twice — including two CONTRADICTORY permutations for the same pair — before any Z3 call is attempted, and is now enforced unconditionally even on an EMPTY batch (`compute_fol_metrics([], [], converses=...)` validates just as strictly as a non-empty one, both structurally AND for method compatibility — a non-empty `converses` combined with `method` in `{exact, canonical, predicate_align}` raises `ValueError` regardless of batch size, matching `equivalent()`'s own gating exactly). `converse_axioms` builds one closed `∀v0..v_{n-1} (A(v0..) ↔ B(v_perm[0]..))` biconditional per declaration. `eval.equivalence.equivalent(..., converses=...)` threads this through the SOLVER level only — the three structural levels raise `ValueError` immediately, and any verdict using it is tagged `method_used="solver_modulo_converses"`, never merged into a plain `"solver"` verdict; a modal formula pair with declared converses raises `NotImplementedError` (no modal bridging route exists), and the MCP `compare_formulas`/`score_batch` tools now catch that alongside `ValueError` so it surfaces as their documented structured error shape rather than an uncaught exception over the wire. `eval.metric_hf.compute_fol_metrics(..., converses=...)` adds a `converse_matched_rate` key under the same non-folding discipline `solver_unknown_rate` already established. The MCP tools accept the same declarations as JSON dicts (`{"a": [name, arity], "b": [name, arity], "permutation": [...]}`), and `compare_formulas` additionally reports `converse_axioms_applied`.

On soundness: this kit's entire classical Z3 export uses exactly ONE Z3 sort for every term, with a predicate interned purely by `(name, arity)`, so a plain, unsorted converse axiom always interns to the identical Z3 function the compared formulas themselves use, many-sorted input included — confirmed by direct code inspection and a differential test pair under `SortedQuantifier` input.

### `hol.free` — free logic, guarded into HOL

Free logic (`semantics.free_logic`) drops classical FOL's assumption that every term denotes an existing individual, so plain universal instantiation is no longer sound. `hol.free` embeds it into THF and Isabelle/HOL the way `to_thf_msfol` embeds sorts, by guard-relativization, with two uninterpreted guard predicates over one individual type: `D(t)` ("t denotes") guards every atom, `E!(t)` ("t exists", narrower than `D` through the tie `E!(x) → D(x)`) guards every quantifier, and the object-language `E!` of `free_logic` is that same guard. The denotation guard also covers every compound subterm, `D*(f(s)) = D*(s) ∧ D(f(s))`, since `f(s)` cannot denote when `s` does not while a HOL function is total. `=` is HOL's own identity under the guard, because `free_holds` compares referents by identity; under `policy="positive"` a self-identity atom is exempt from the guard, matching `free_satisfies`'s carve-out. The tie is the only background fact: an empty inner domain is a free-logic model, so there is no `∃x E!(x)`. The module docstring spells out why a HOL proof is then a free-logic validity and a genuine HOL countermodel a free-logic countermodel.

The first version of the embedding rendered `=` between different terms as an uninterpreted `feq`, guarded only the outermost term, and added `∃x E!(x)` as a premise. `isabelle_decide_free` then called `∀x ∀y ((x = y ∧ P(x)) → P(y))` invalid and `(∀x P(x)) → ∃x P(x)` valid, the opposite of `free_is_valid` in both cases; the adversarial review had checked only the direction from a free-logic model to a classical structure, which cannot see a spurious HOL countermodel. The tests now check both directions offline: the guarded formula evaluated on structures built from hand-made `FreeModel`s (including a partial function and an empty inner domain) against `free_holds`, and the bounded classical model finder run on the emitted problem itself against `free_is_valid` — this second check fails for each of the three defects. Live Isabelle tests pin the three regressions.

`policy="supervaluation"` is refused with `NotImplementedError` from every entry point: supervaluationist truth is a property of a whole model's gap assignment, not something a single guarded formula can state without second-order quantification over gaps. A predicate literally named `D!` is refused with `ValueError` rather than silently merged with the guard. `to_thf_free` / `to_isabelle_free` mirror `to_thf_fol` / `to_isabelle_fol`; `free_theory` and `isabelle_decide_free` wire the embedding into the Isabelle runner next to `isabelle_decide_fol`.

### `semantics.kripke` — CTL model checking: `ctl_ex`/`ctl_af`/`ctl_eg`/`ctl_au`

`KripkeModel`'s temporal fragment covered only the four LTL-style modalities baked one-per-AST-node into `Next`/`Always`/`Eventually`/`Until` (Next and Always read universally, Eventually and Until existentially) — there is no A/E path-quantifier prefix anywhere in the grammar, so full CTL needed the other four readings as plain functions, not new dispatch branches, exactly like `common_knowledge_holds`/`everybody_knows` in `semantics.action_models`. `ctl_ex(model, world, φ)` is the existential dual of the built-in universal `Next`, a one-step modality with no fixpoint and no totality requirement — a dead end simply makes it `False`, the dual of `Next`'s vacuous `True` there. `ctl_af(model, world, φ)` and `ctl_eg(model, world, φ)` compute the least fixpoint `μZ. φ ∨ AX Z` and the greatest fixpoint `νZ. φ ∧ EX Z` (Baier & Katoen §6.4) by forward/backward iteration on the `"temporal"` relation restricted to `model.worlds`, each converging in at most `|model.worlds|` rounds — no external library and no Tarjan/SCC machinery, since none is required for correctness. `ctl_au(model, world, φ, ψ)` is the universal-path generalisation of the kit's existing (existential) `Until`, the least fixpoint `μZ. ψ ∨ (φ ∧ AX Z)`. Because AF/EG/AU quantify over infinite paths, all three require the `"temporal"` relation to be total on `model.worlds`; a dead-end world raises `ValueError` naming it, rather than silently adopting `Next`'s vacuous-true convention — the same refuse-loudly discipline `product_update` already applies to a missing agent relation. Verified three ways: property-based duality/entailment checks (`AF φ ⇔ ¬EG¬φ`, `AU(φ,ψ) ⊨ AF ψ`, `AG φ → AF φ ∧ EG φ`) over random total models; an independent brute-force differential that enumerates every lasso path (a finite simple prefix plus a simple cycle) reachable from a world and decides AF/EG/AU by explicit path quantification, sharing no code with the fixpoint implementation; and a hand-checked mutual-exclusion fixture plus a dedicated dead-end fixture pinning the deadlock convention. New tests in `tests/test_ctl.py`; documented with a worked mutex example in the model-checking guide.

### `semantics.model_eval` / `atp.finite_domain` / `atp.clingo_backend` / `atp.minizinc_backend` — function symbols close the last real fragment gap

`Function` used to sit in the same place `Cardinality`/`Count` did before 0.22.0's own closure: `ClingoBackend`/`MinizincBackend` could ground and solve a function-bearing sentence, but `fragment_check` refused it BY NAME up front, because `semantics.model_eval` — the independent checker `verify_model` is required to call before either backend may report `REFUTED` — had no case for a `Function` term at all. That refusal is now closed by the identical mechanism the counting fragment already got: `model_eval._term_value` gains a `Function` case that resolves `f(t1,...,tk)` off the same `(name, arity+1)` "total relation" extension `atp.finite_domain.structure_from_solution` already reconstructs for a function symbol — the unique row whose leading `k` components match the (recursively evaluated, so nested composition `f(g(x))` needs no special case) arguments — refusing loudly, by a named `ValueError`, if that row is missing (the function is PARTIAL in a hand-built structure) or not unique (the relation is not FUNCTIONAL), mirroring the uninterpreted-symbol pattern the evaluator already uses elsewhere. `fragment_check` now admits `Function` generally, so both backends' previously-dormant `Function` encoders (`_AspEncoder._term`'s choice-rule total-relation encoding; `MinizincBackend`'s `array[DOM, ...] of var DOM` declaration, already documented, never reachable) are live: a function-bearing countermodel is now genuinely grounded, solved, reconstructed AND independently re-verified end to end, e.g. "f is an involution" (`∀x (f(f(x))=x)`) REFUTED with `detail=None` at the hand-derivable minimal domain size 2.

The four arithmetic operator names (`+`, `-`, `*`, `/`) and comparing a domain individual with a bare numeral both stay refused exactly as before — no new code was needed for either: `Signature.from_formulas`'s pre-existing `_BUILTIN_FUNCS` carve-out already keeps the four names out of a problem's declared `functions`, so each backend's own "symbol not declared in signature" error catches them naturally; and `Function` terms are evaluated only through `_term_value`/the new `_function_value`, never through `_numeric_value` (which alone reads `Cardinality`/`Number`), so the two paths share no lookup and this closure cannot reintroduce the numeral-read-as-a-structure-constant confusion `semantics.tarski` had to fix separately.

A new, narrow, explicit refusal closes a real hazard the many-sorted work opened: a *sorted* function declaration (`FunctionDecl.arg_sorts`/`result_sort` set) is refused, loudly, in `FiniteDomainProblem.__post_init__` — neither backend's function encoder consults those fields at all, and `FiniteStructure` has no sorts concept to check a sort-respecting graph back against even in principle, so admitting one silently would have meant quietly ignoring a caller's own stated constraint. This refusal is provably inert on the live `decide()` path of either backend (`Signature.from_formulas` never sets those fields), the identical "defense in depth, not the live path" shape the sorted-quantifier-family refusal already has at `fragment_check`.

A function-bearing variable is not indexed by the existential/`Count` candidate-narrowing heuristic (`_variable_candidates`) when it occurs only inside a `Function` argument — this stays SOUND with no code change (the heuristic's own `isinstance(Variable)` checks simply do not match a `Function`-wrapped occurrence, so such an atom contributes no narrowing and the variable falls back to the documented full-domain scan), now stated explicitly in the module docstring rather than left implicit.

Differentially tested three ways: against `semantics.modelfinder.find_countermodel` (the kit's own from-scratch, brute-force, independently Function-capable model finder) over three small hand-checked algebraic theories refuting commutativity/associativity/idempotence of an explicit binary table; against `semantics.tarski.satisfies` over an equivalent `tarski.Structure` built from the same reconstructed extension data; and via a live `clingo` 5.8.1 solver run end to end for every case (`tests/test_finite_domain_functions.py`, `tests/test_clingo_backend.py`).

### `eval.explain` — `explain_proof`: the validity-side counterpart of `explain_countermodel`

`explain_proof(proof, *, max_sentences=6)` renders any proof object the atp layer actually attaches to `Verdict.proof` as a short, deterministic English paragraph, mirroring `explain_countermodel`'s own architecture — deterministic sorting, a sentence-priority list per shape, `max_sentences` truncation, and a loud `TypeError`/`ValueError` on anything unrecognised rather than a silent guess — for the validity side of a verdict instead of the invalidity side. Five shapes reach `Verdict.proof` today, confirmed by grepping every backend that populates it, and every one is covered: `atp.tableau.TableauProof` (`TableauBackend`) is reported as step count, a sorted rule-application histogram, closed-branch count, and one sentence per closure naming its two closing literals (or its bare `⊥` self-closure) sorted by `leaf_id`; `atp.tstp.TstpDerivation` (`VampireBackend` and `EProverBackend` — the same shape, one renderer) as step count, the sorted set of roles present, and the final step's rule together with a backward breadth-first trace of every ancestor reachable through its parent DAG, not just one arbitrarily-chosen path; `atp.twee_entailment.TweeProof` (`TweeBackend`) as axiom/lemma counts and the goal's rewrite chain with its citations, R->L direction included; and the two solver-level proof dicts that carry no dataclass of their own, `{"kind": "z3_unsat_core", ...}` (`Z3Backend`) and `{"kind": "cvc5_alethe", ...}` (`Cvc5Backend`), as their tracked-term unsat core (and, for cvc5, its Alethe proof's non-blank line count). Every typed proof object is accepted directly, and so is the plain dict `Verdict.proof` actually carries once round-tripped through `.to_dict()` (or the process-pool boundary) — the five shapes' key sets are disjoint, so dispatch never has to guess. Fitch `Proof`/`Line`/`Justification` chains are deliberately not covered: `atp.fitch_search` builds them, but no `ProverBackend` currently attaches one to `Verdict.proof`, so there is no live caller through the eval/atp protocol layer to explain yet — a natural follow-up once/if one is registered.

### `ilp.IlpTask` — Aleph's mode/determination bias and example-file emitter, alongside Popper's

`IlpTask` gains a second emission path next to the existing Popper writer, reusing its constructor's anti-leakage checks and `background_text()` unchanged — only the bias and example renderings are learner-specific. `aleph_bias_text()` emits Aleph's `modeh`/`modeb`/`determination` mode/determination bias (`:- modeh(1, target(+example)).`, one `modeb` per body predicate under a single documented convention — first argument bound `+individual`, the rest free `-individual`, since `FiniteStructure` carries no per-argument sort to derive a real mode pattern from — and one `determination/2` line per body predicate including membership); `max_body` translates to Aleph's `:- set(clauselength, N).`, while `max_vars` and `max_clauses` are named in a comment rather than silently dropped, since Aleph has no single-clause equivalent for either (its clause count comes from `induce`'s own covering loop, not a bias-file bound). `aleph_examples_text(label)` emits Aleph's `.f`/`.n` convention — bare ground atoms split by label, genuinely different from `examples_text()`'s `pos()`/`neg()` wrapper — and `write_aleph(directory, filestem="task")` writes the classic `<stem>.b`/`.f`/`.n` triple, `.b` carrying background facts and bias concatenated exactly as Aleph itself expects them, where `write()` keeps Popper's three files separate. The mode convention and file layout were checked against a real Aleph, not just its manual: the SWI-Prolog `aleph` pack's `aleph_orig.pl` loads the emitted `.b`/`.f`/`.n` triple with no `example/1`/`individual/1` type fact of any kind — Aleph's `+type`/`-type` binds purely from resolving the real background predicates during saturation, never from enumerating a declared type predicate — and `induce` learns the intended target clause from it. `tests/test_ilp_aleph.py` carries that as a skip-gated live test (network-free, installs nothing, skips cleanly with no SWI-Prolog+aleph reachable) alongside a fast, tool-free differential check that re-parses the emitted `.f`/`.n` bare atoms and `examples_text()`'s own `pos`/`neg` output through the kit's Prolog reader and confirms they describe the same labelled example set.

### `atp.fitch` / `atp.sequent` — HTML rendering for Fitch proofs and sequent derivations

`Proof.to_html()` (`atp.fitch`) and `Derivation.to_html()` (`atp.sequent`) render a Fitch natural-deduction proof and a Gentzen sequent-calculus derivation as self-contained, theme-aware HTML pages, in the exact idiom `fol.derivation.CCGDerivation.to_html()` already established (a `<!doctype html>` page, CSS custom properties themed via both `prefers-color-scheme: dark` and an explicit `data-theme` override, HTML-escaped user text). `Proof.to_html()` is a straight sink of the already-computed `_visual_rows` shape `render_fitch` itself consumes: a numbered line gutter, one nested `border-left` cell per open subproof (the vertical Fitch scope bars), and a horizontal rule under the premises and under each assumption. `Derivation.to_html()` mirrors CCG's `.nd`/`.pr`/`.bar`/`.cn` flex-tree layout, generalized from CCG's binary combinator tree to a sequent rule's arbitrary premise arity, with the rule name — and, when present, the instantiation term / eigenvariable / `Comprehension` — to the bar's right, exactly as `render_sequent_proof`'s bracketed label already surfaces `extra`. The escaping helper and the page wrapper/colour-token skeleton live in a new private `atp._html` module shared by both renderers, kept out of `fol/derivation.py` deliberately so the established one-way `atp` → `fol` module-level dependency direction stays intact — `CCGDerivation.to_html()`'s output is untouched, pinned by a byte-for-byte regression test. Resolution-proof and ILL/Lambek HTML rendering remain out of scope for this item.

### `atp.protocol` — `Verdict.solver_version`: which build of an external prover actually answered

Two verdicts from the same backend NAME can come from genuinely different tool builds — a Vampire binary upgraded mid-project, a re-pulled HETS image, a bumped `cvc5` pip package — and nothing on `Verdict` said which. `Verdict` gains `solver_version: Optional[str] = None`, and `ProverBackend` gains an optional `solver_version() -> Optional[str]` method (default `None`, matching every internal backend — Z3/tableau/resolution/modelfinder/QML/…, which have no external tool to version). The routes with a genuine external tool behind them override it: `VampireBackend`/`Prover9Backend`/`EProverBackend`/`ZipperpositionBackend` spawn `<binary> --version` once per `(binary, use_wsl)` pair through a new process-local memoized `atp.protocol._binary_version`; `HetsBackend` calls the already-existing but until now unused `HetsClient.version()` once per discovered server URL; `Cvc5Backend` reads `importlib.metadata.version("cvc5")` once. Every lookup degrades to `None` on any failure rather than ever turning a sound PROVED/REFUTED verdict into an ERROR one — including, now, a `--version` banner that fails to decode under Python's default text encoding (`_binary_version` catches `UnicodeError` alongside the subprocess/timeout failures it already handled, so a non-UTF-8 banner degrades to `None` instead of crashing a working `decide()` call) — and none of the five spawns more than one subprocess/HTTP/importlib round trip per binary/server/package for the life of the process. `eval.batch.batch_decide`'s content-addressed `_cache_key` now folds each effective backend's own `solver_version()` in alongside the material it already covered, computed once per cache-missing task in the parent process before any `ProcessPoolExecutor` dispatch.

`HetsBackend.decide()` now carries `solver_version` on an out-of-fragment formula's UNKNOWN/"unsupported" verdict too, when the caller passed an explicit `url=` server override (they already opted into contacting that specific server, so this adds no network touch beyond what was asked for); without an explicit `url=`, that branch still reports `solver_version=None`, preserving the deliberate contract that an unsupported formula never causes `decide()` to touch the network via auto-discovery.

Found along the way: `atp.portfolio._verdict_from_dict` — the `jobs>1` process-pool path's only way back from a worker's JSON-safe dict to a live `Verdict` — silently dropped `relevant_premises` (and would have dropped `solver_version` too) instead of round-tripping every field; both now round-trip.

`hets.docker.HETS_IMAGE` is now digest-pinned (`spechub2/hets@sha256:406dcf34fb2486a99829a57583a2b247163ed99d1f9ace2d66ebedab9d47528a`) rather than the movable `:latest` tag, to the exact build (HETS 0.108.0) the module docstring already claimed to have verified.

### `hol.isabelle_relevant` / `hol.isabelle_conditional` — a THF route for relevant logic B and Lewis counterfactuals

`to_isabelle_relevant` and `to_isabelle_conditional`/`isabelle_conditional_theory` had no THF sibling — `hol.thf_modal` even refused `□→`/`◇→` by name, pointing the caller at the Isabelle-only route, while every other shallow embedding in the package already had one. `to_thf_relevant(φ)` and `to_thf_conditional(φ, *, centering="weak")` close that gap: the same shallow embeddings — `N`/`star`/`R` uninterpreted over Routley–Meyer worlds, `Sel` uninterpreted over Lewis spheres, the frame conditions bundled as **premises** of the conjecture rather than axioms, exactly as the Isabelle route already does it — emitted as a self-contained TH0 problem for Leo-III / Vampire-THF / Satallax instead of an Isabelle theory. Both THF exporters deliberately diverge from a literal transcription of their Isabelle preamble in one respect: the propositional connectives are inlined at the current world rather than routed through named combinators, and the frame/centering predicates are stated directly of the one fixed `N`/`R`/`Sel` rather than as a schema over an arbitrary one — both meaning-preserving changes, made because the literal transcription needed genuine higher-order unification and could not close even trivial goals against Vampire 5.0.1's default portfolio within 60 seconds, while the inlined form closes in well under one. Both routes are cross-checked in **both directions** against Vampire 5.0.1 (via WSL) over their respective hand-checked test batteries: every valid schema is proved `Theorem`, and every invalid schema's own bounded countermodel (`rel_countermodel` / `cf_countermodel`) is independently re-derived as a refutation by Vampire from closed-domain ground facts routed through the very same `_thf_encode` the exporter ships — with one documented exception class on the conditional side (`_VAMPIRE_SLOW_INVALID`): refuting a `□→` whose antecedent is satisfiable within some sphere of the countermodel asks Vampire to synthesise a higher-order witness for an existential over sphere-functions, which its default portfolio does not always close quickly (never a wrong verdict — the observed failure mode is `Timeout`, not a false `Theorem`/`CounterSatisfiable`). `to_isabelle_conditional`/`isabelle_conditional_theory`, present since release 0.19.0 but never reachable from `unicode_fol_kit.hol`'s own public surface, are exported for the first time alongside their new THF sibling.

### `fol` / `semantics.action_models` / `atp.modal_tableau` — group-epistemic operators: everybody-knows, distributed knowledge, common knowledge

Three new AST nodes close the standard group-epistemic trio next to the existing single-agent `Knows`: `EverybodyKnows(group, φ)` (E_G φ ≡ ⋀_{a∈G} K_a φ, one step over the UNION of the group's `"K:"+agent` relations), `DistributedKnowledge(group, φ)` (D_G φ, one step over the INTERSECTION — the logically weakest of the three, yet the one that pools every agent's information; an empty group is refused at construction, since an intersection over zero relations is conventionally the universal relation), and `CommonKnowledge(group, φ)` (C_G φ, the reflexive-transitive closure of the group's union relation — NOT first-order definable, so `standard_translation` refuses it by name exactly as it already refuses `Until`/`Since`). `semantics.action_models` gains `distributed_knowledge_holds` alongside the existing `common_knowledge_holds`/`everybody_knows`, and the Kripke evaluator dispatches each new node straight to its matching function, the same thin-AST-wrapper pattern `Announce` already uses.

Surface syntax is `GLYPH_{agent,agent,…} φ` — `C_{a,b,c} φ`, `D_{a,b} φ`, `E_{a,b,c} φ` — each opening glyph its own fused terminal (`C_{`/`D_{`/`E_{`) so the lexer never has to choose between it and a same-length predicate name; an agent is an ordinary VARIABLE or NAME term, comma-separated, so a group member can be bound by an enclosing quantifier (`∀x (Student(x) → E_{x,b} φ)`) and resolved by the same `resolve_agent_variables` scope pass every single-agent modality already uses. The grammar itself requires at least one agent, so the parser can never build an empty group.

The labelled tableau's distributed-knowledge closure (`_close_distributed`) computes a `D_G` box's synthetic intersection relation from its constituent `"K:"+agent` relations, but previously never registered those constituents as live for frame closure — an agent mentioned ONLY inside a `D_G` box never received the caller's requested frame conditions (S5 reflexivity and friends), so `D_{a} P → P` could wrongly decide invalid under S5, with `modal_countermodel` reporting a spurious, non-frame-closed "S5" countermodel. `_close_distributed` now registers each constituent `"K:"+agent` relation in the branch's relation table the first time its synthetic intersection key is seen, and reports that registration as a change so the tableau's fixpoint loop runs frame closure again before treating the intersection as final — verified directly: `D_{a} P → P` and `D_{a,b} P → P` now decide valid under S5 (matching the `Knows(a,P) → P` control), stay invalid under plain K, and the wrong-direction `D_{a,b} P → K_a P` stays correctly invalid under S5 too, with a genuinely frame-closed countermodel.

`atp.kripke_enum` and `atp.fitch` keep their own scan of which relations a formula uses, and both now count every member of a group operator. Without that, the finite-model search fixed a member's relation empty on every candidate, which under an epistemic S5 system is not a legal frame at all, so it "refuted" the valid `E_{a} P → P` and `D_{a} P → P`; Fitch checking only rejected the valid S5 step instead. A group operator nested under another operator (`¬E_{a,b} P`, `K_a P ∧ K_b P → E_{a,b} P`) also renders now: the shared renderer delegates to the node's own form, as it already did for announcements, and the text parses back to the same tree. Every other route that has no rule for the new nodes refuses them by name — normal forms, the many-valued evaluator, announcement reduction, the QML translation and the HOL modal exports.

### `eval.datasets.pmb` — the Parallel Meaning Bank joins the adapters, gold FOL parsed straight from SBN

Unlike every other adapter in this package, PMB ships no ready-made NL/FOL pair file — its unit of data is one directory per annotated document (`p<NN>/d<NNNN>/`), holding a DRS in SBN notation (`<lang>.drs.sbn`) plus the sentence(s) it annotates (`<lang>.raw`). `load_pmb(paths, *, known_bad_ids=None)` walks a release directory (or reads a caller-supplied file list) and produces gold FOL through the existing `drt.parser.parse_sbn` / `drt.export.drs_to_fol` pipeline: `id` is PMB's own `p<NN>/d<NNNN>` address, `nl_conclusion` is the sibling raw text (best-effort, `None` when absent), `fol_conclusion` is `drs_to_fol(parse_sbn(text)[0]).to_unicode_str()`. A document whose SBN raises `SBNSyntaxError` is never silently dropped: it still yields a `DatasetExample` with `fol_conclusion=None` and the refusal recorded verbatim in `meta["parse_error"]`, following the same refuse-loudly discipline `parse_sbn` itself already follows, carried one level up instead of aborting the whole generator on the first bad document.

Measured against pmb-5.1.0's complete English gold release (12053 `data/en/gold/p*/d*/en.drs.sbn` files): 9624 (79.8%) parse AND round-trip through the kit's own FOL printer/parser; every one of the remaining 2429 raises `SBNSyntaxError` naming an out-of-scope construct (wildcard role targets, SDRT discourse relations and modal boxes this DRS subset has no reading for, clock-time constants, non-WordNet-shaped sense tokens, and a long tail of one-off constant kinds) — none crashes. This is a robustness/coverage measurement, not a translation-accuracy one, since PMB ships no independent gold FOL to compare against.

License is two-layered and the two layers are NOT the same: the PMB annotations (the DRS/SBN layer this loader parses) are ODC-BY 1.0, attribution required, per the release's own `licenses/PMB_LICENSE.txt`; the raw texts (`nl_conclusion`) are explicitly NOT covered by that license — `PMB_LICENSE.txt` defers each raw sentence to its own subcorpus's terms, recorded only as a `subcorpus:` label and a `source:` URL in the document's `.met` file, so a caller who wants to redistribute `nl_conclusion` text must trace that source themselves. `DATASET_INFO["pmb"]` records the two-layer license explicitly rather than picking one.

### `eval.datasets.pfolio` — P-FOLIO's derivation chains, joined onto its own bundled FOLIO.csv

P-FOLIO adds one thing FOLIO's own JSONL distribution does not carry: a human-written, step-by-step derivation for every (story, conclusion) pair. The release ships as two CSV files rather than JSONL — `P-FOLIO.csv`, a spreadsheet export where a digit-only `story_id` row opens one conclusion's derivation block and every following row is one step (`Derivation index` `D1`, `D2`, …, sometimes with the FIRST step's own content sitting on that same header row rather than a later one — verified on 164 of the real file's 1431 blocks, all correctly captured, not dropped), and P-FOLIO's own bundled `FOLIO.csv`, one row per story with newline-joined premise/conclusion lists — verified directly against a real download rather than assumed from the paper. Neither file carries a shared conclusion id, so `load_pfolio(pfolio_path, folio_path, ...)` joins on story id AND a block's position among its story's blocks, and CROSS-CHECKS every join: the block's own truth value must agree with `FOLIO.csv`'s truth value at that position, or the block is refused, never guessed. Re-measured through the loader against the real, once-downloaded files: of 1431 blocks, 1420 load and 11 are refused — 5 genuine truth-value disagreements between the two files, 3 reviewer comments left in the truth-value cell instead of a real `T`/`F`/`U`, 2 stories whose `Conclusions - NL` column holds premises instead of conclusions (a real upstream defect), and 1 story with more P-FOLIO blocks than resolvable FOLIO conclusions — every one traced back to a specific story id in the module docstring and `pfolio_refusals()`. `Derivation` and `Derivation - Corrected` stay two distinct keys in `meta["proof_steps"]`, never merged, since the corrected text sometimes reads quite differently from the original; `Premises used` is kept as one raw string rather than parsed into indices, since the real column mixes plain premise numbers, `D`-prefixed step references, and both comma and full-width-comma separators in the same cell. License MIT per the yale-nlp/P-FOLIO Hugging Face dataset card; the source is access-gated, so tests run against a small hand-written fixture in the real CSV layout, with an opt-in test re-measuring the documented counts from `$UFK_PFOLIO_CSV`/`$UFK_FOLIO_CSV`.

### `eval.datasets.logicbench` — LogicBench: 25 single-inference-rule reasoning patterns, one route per logic type

LogicBench joins the dataset adapters, modeled directly on `fracas`'s no-gold-FOL contract: every row is natural-language context plus a question and a `yes`/`no` (BQA) or multiple-choice (MCQA) answer, nothing more, so the translation step lives outside this library (`solve_example`'s injected `translate`). `load_logicbench(path, split="BQA"|"MCQA")` reads one `LogicBench(Eval)` `data_instances.json` — `context` maps to the single-element `nl_premises`, the question to `nl_conclusion`, and the gold answer to `label`, kept verbatim rather than smoothed into FraCaS's yes/no/unknown three-way scale, since a binary QA task and a 4-or-5-way multiple choice are different task shapes. A BQA sample's `qa_pairs` (2-4 per sample, each asking about a different proposition) flattens into one `DatasetExample` per pair, `meta["qa_index"]` marking the split point; an MCQA sample's fixed meta-question and `choices` dict survive in `meta` unchanged. `meta["axiom"]`/`meta["logic_type"]` carry the source file's own inference-rule and logic-type labels — verified directly against the real files that the non-monotonic split's own `"type"` value is `"non_monotonic_logic"`, never the literal `"nm_logic"` its directory happens to be named (`NM_LOGIC_TYPE`).

`solve_example` decides BQA rows only (an MCQA row's `question` is a generic meta-question, not a standalone proposition, so it is refused by name) and routes on `logic_type`: `propositional_logic`/`first_order_logic` through `api.prove` as FraCaS does, `predicted=None` on an inconclusive verdict rather than forcing LogicBench's `{yes,no}`-only label space to guess; `non_monotonic_logic` through `semantics.nonmonotonic.minimal_entails` — a genuine reuse of the kit's own circumscription evaluator, not a second classical cascade. The route refuses when no minimal model exists within `max_size` (catching `minimal_entails`'s own vacuous-True case), but honestly does NOT detect the separate case of several minimal models disagreeing on the goal — a translation that leaves an abnormality predicate unpinned for some individual gets `minimal_entails`'s own skeptical bool with no flag that the question was underspecified, documented in the module and pinned by a dedicated test rather than left implicit.

License MIT per the cloned repository's own `LICENSE` and README, not the CC BY 4.0 the original roadmap proposal assumed (`DATASET_INFO["logicbench"]` records the correction). AR-LSAT, bundled with LogicBench in the same proposal, stays excluded — already investigated and rejected (no shipped gold annotation, copyright-encumbered LSAT passages), per the existing note in this package's docstring.

### `eval.theory_check` / `eval.chem_batch` — Markdown and HTML report rendering

`TheoryReport.to_markdown()` / `TheoryReport.to_html()` and `ChemBatchResult.to_markdown()` / `ChemBatchResult.to_html()` render the two batch-verification result types as either a plain Markdown document or a self-contained, theme-aware HTML page, in the same idiom `fol.derivation.CCGDerivation.to_html()` and the `atp` Fitch/sequent renderers (`atp._html`) already established. `TheoryReport`'s renderers cover its three sections — the cycle chains `find_cycles` found, `satisfiability` grouped by status, and `subsumptions` grouped by status — with every name/detail/explanation routed through a shared string-safety helper (`_md_cell` for Markdown, `esc_html` for HTML) so a hostile definition name or error message (one containing `|`, a newline, or HTML metacharacters) cannot corrupt the table structure. `ChemBatchResult`'s renderers are deliberately a SUMMARY, not a row dump — a campaign run is hundreds of thousands of rows — rendering `counts`/`cache_stats`/`seconds`/`skipped` as summary tables plus an explicit, capped sample of at most `max_rows` non-`ok` rows, always closing with an honest "showing N of M" note rather than a silent truncation. Calling either renderer twice on the same result is byte-identical: no rendering path depends on dict/set iteration order, every grouping walks the same fixed, sorted order `to_dict()` already uses.

Both renderers gloss a result's evidence only under the ONE status each is documented to occur for, never unconditionally on a truthy field: a `SubsumptionResult.countermodel` is only rendered as refutation prose under `status="refuted"` (the only status `check_subsumption` itself ever attaches one to), and a `SatisfiabilityResult.witness` is only rendered as a satisfying-assignment gloss under `status="satisfiable"`. Neither result's `__post_init__` forbids a hand-built object from carrying a countermodel/witness alongside a different status, so without this gating a stray witness on an `"unknown"`/`"unsatisfiable"`/`"cyclic"` result would render self-contradicting text — explicit refutation prose under an `### unknown` heading, or a satisfying assignment next to a reported contradiction — misdescribing a result the module's own docstrings promise stays honestly undecided or negative.

### Many-sorted quantification now combines with modal and second-order logic

`MSFLParser(modal=True)` and `MSFLParser(second_order=True)` each combine with `many_sorted=True` now, e.g. `□∀x:Human (Mortal(x))` and `∀P (∀x:Human P(x) → ∃x:Human P(x))` — the one combination that stays refused is `third_order=True` with `many_sorted=True` (how a sort interacts with third-order's individual-vs-property "slot" inference needs its own design pass). Every consumer delegates to `SortedQuantifier`'s existing `_relativize` reduction (`∀x:S φ` → `∀x (S(x) → φ)`, `∃x:S φ` → `∃x (S(x) ∧ φ)`) rather than reimplementing sorted semantics per route: the Kripke evaluator (`satisfies_modal`), the QML first-order shallow embedding (`fol.qml`), both HOL exporters (`hol.isabelle_modal`, `hol.thf_modal`), and the intuitionistic Kripke search (`semantics.intuitionistic`) all gained a working path for a `SortedQuantifier` where they previously raised `NotImplementedError`/`ValueError` outright, and for a bare sorted constant occurring anywhere in the formula (not only under a binder).

Two semantic choices the relativisation itself does not make, decided and documented consistently across every route: a sort guard is WORLD/STAGE-RELATIVE rather than rigid (an individual can be `Human` at one world and not at another — the same "actualist" reading this kit already gives the bare per-world object domain), and NON-EMPTINESS of a sort is a per-route choice rather than automatic everywhere — matching the classical routes' own always-on convention (`fol.nonempty_sort_axioms`, added as extra premises) would silently assume something the modal/intuitionistic routes have no domain-construction step to enforce. `satisfies_modal` never assumes it (the caller builds a model where a sort's guard holds where it needs to, the same responsibility it already has for domains/valuation); every route that answers a VALIDITY question does — `qml_is_valid`, `int_valid`/`int_countermodel` and both HOL exporters thread the assumption in automatically — `fol.qml.qml_axioms` gains one non-emptiness axiom per sort per world (mirroring its existing `nonempty_dom` axiom for the bare object domain), and `semantics.intuitionistic` folds the same non-emptiness sentences in as an extra premise (`⋀nonempty-axioms → relativised-formula`, sound both classically and intuitionistically for a finite premise set) — and `hol.isabelle_modal` / `hol.thf_modal` emit one `nonempty_sort<i>` axiom per sort beside their existing `nonempty_dom` (listed by `modal_axiom_names`, so a generated `using … by …` proof has them in scope; `existsAt`-guarded under an actualist `mode`, since only the local domain can instantiate the existential) — so a modal-free many-sorted schema like `∀x:S P(x) → ∃x:S P(x)` agrees with `api.prove`'s classical verdict through EVERY one of those routes, while a bare Kripke model without that construction is honestly evaluated exactly as built. Without the HOL axioms the two exported problems were the odd ones out: an external prover would have failed to close exactly that schema.

The parser gains two grammar modes, `MSFLParser(modal=True, many_sorted=True)` and `MSFLParser(second_order=True, many_sorted=True)`, assembled the same registry-cloning way `third_order_modal` already is — except cloning has to actively EXCLUDE `modal`'s/`second_order`'s own unsorted individual-quantifier and counting-quantifier operators (`fol.nodes._clone_parser_ops_sorted`), since a naive clone would otherwise accept an unsorted `∀x` right alongside the sorted `∀x:S` many_sorted is supposed to forbid. The sorted modal mode also joins the LALR-first, Earley-fallback wrapper (`_HYBRID_MODES`) — it inherits the modal family's hybrid-logic nominal operators wholesale, and with them the one documented LALR/Earley grammar conflict.

`satisfies_modal` relativises many-sorted input ONCE, at the top of the evaluation, rather than only where recursive descent happened to walk into a `SortedQuantifier` — a bare sorted constant occurring as a ground fact with no enclosing quantifier (e.g. `Mortal(alice:Human)`) used to keep its `:Sort` suffix all the way to the valuation lookup and silently evaluate `False` regardless of the model. This is now caught by relativising the whole formula up front, alongside a deep pre-scan that refuses a Łukasiewicz/lambda node nested under a modal operator by name rather than letting it slip through — previously possible when such a node happened to have zero successors and so was never reached by the top-node-only check that used to guard it.

### `atp.logic_backends` — five per-logic `ProverBackend` adapters, not a uniform bulk registration

`IntBackend`, `LambekBackend`, `IllBackend`, `RelevantBackend`, and `HybridBackend` wire the kit's five existing substructural/non-classical decision procedures — `atp.lj.int_prove` (Dyckhoff's G4ip), `atp.lambek.lambek_derivable`, `atp.linear.ill_derivable`, `semantics.relevant.rel_countermodel`, and the standard translation into a tracked Z3 `Solver()` for hybrid logic H(@) — into the uniform `Verdict` protocol, each reasoned about on its own terms rather than mechanically registered behind one shared shape. `LambekBackend` reads `premises` as the LITERAL ORDERED antecedent, bypassing the shared classical `∧`-fold entirely (order-sensitivity is pinned by a direct regression). `IllBackend` detects `!` via `_has_bang` and reports a definitive REFUTED only on the `!`-free fragment AND when the depth budget in force (default or caller-supplied) is at least the sequent's own safe/complete bound (`total` size, or `2*total+4` once `!` occurs — exactly `ill_prove`'s own default); a caller-supplied `max_depth` below that bound, or any `!`-bearing sequent, reports UNKNOWN(bound_hit) instead — never a false REFUTED. `RelevantBackend` NEVER reports PROVED (`rel_valid`'s bounded Routley–Meyer search is sound but incomplete), and a REFUTED witness is a fully serialized `RelevantModel` that round-trips back through `rel_satisfies`. `HybridBackend` deliberately bypasses the bare-bool `hybrid_is_valid`, instead reusing `standard_translation`/`_frame_axioms` and the kit's own tracked per-call `Solver()`, so a genuine countermodel (SAT) is never conflated with a solver timeout (UNKNOWN). `IntBackend` rejects quantified input up front and attaches a best-effort Kripke witness on REFUTED — the REFUTED status itself is always definitive (from `int_prove`), though the witness search can occasionally come back empty for a genuine non-theorem, since its bounded search's finite-model-property depth grows with the formula.

Five new singleton default chains join the registry (`"intuitionistic"`, `"lambek"`, `"ill"`, `"relevant"`, `"hybrid"`), and `api.prove(logic="auto")` now detects `"lambek"`/`"ill"`/`"hybrid"` from an unambiguous syntactic marker. Intuitionistic and relevant logic reuse the plain classical propositional AST with no marker of their own, so `logic=` must still be given explicitly for those two. Routing for every pre-existing classical/modal input is unchanged (pinned by a regression battery). The registry now carries 25 backends in total (up from 20 before this addition); `README.md`'s prover-backend count is updated to match.

### `semantics.modelfinder` / `semantics.free_logic` — least-number-heuristic symmetry breaking for the finite model finder

The finite model finder's enumeration revisited every one of a domain's `k!` relabelings of the same underlying structure — a signature with several named constants spent almost its whole search budget on interpretations that differ only by which domain element happens to be called `0` versus `1`. `find_model`/`find_countermodel`/`is_satisfiable_finite`/`is_valid_finite`, `free_logic.free_find_model`/`free_countermodel`/`free_is_valid`/`free_entails`, and (by reuse, no separate implementation) `secondorder.so_find_model`/`so_find_countermodel` now default to a new `symmetry_breaking: bool = True`, which enumerates CONSTANT assignments with the classical least-number heuristic (LNH) instead: in canonical symbol order, each constant is filled with either an already-used domain value or the smallest still-unused one, collapsing `k!` relabelings of a constant assignment into one canonical representative (`modelfinder._canonical_interpretations`). A signature with several named constants sees the dominant cost disappear — a measured 29x-164x wall-clock speedup on representative pairwise-distinct-constants problems (see `docs/guide/finite-domain.md`'s worked example: ~111x on 7 pairwise-distinct constants). Function and predicate tables stay fully exhaustive on both sides of the flag: a hand-checked counterexample (in `modelfinder._canonical_interpretations`'s own docstring) shows that naively extending the same per-cell LNH cap to a function's table — as an earlier draft of this feature called for — is actually UNSOUND, since a function's argument tuple is itself made of domain elements and is not exempt from relabeling the way a constant is; this implementation keeps LNH scoped to constants only, where the restricted-growth-string argument is airtight, and leaves functions exhaustive exactly like predicates already were. `symmetry_breaking=False` recovers the original, byte-for-byte exhaustive enumeration on every affected function, both for differential testing and for a caller who wants the plain search order.

The pre-flight "skip this size" check that decides whether a domain size is worth searching uses an EXACT, purely analytic count of what the LNH-reduced enumeration will yield (`modelfinder._canonical_candidate_count` / `free_logic._canonical_candidate_count`, backed by an `O(n_constants * domain size)` dynamic program over restricted-growth-strings — equivalently, set partitions into at most k blocks — `_lnh_constant_count` / `_canonical_constant_count`), computed BEFORE a single candidate is generated or checked. A size whose exact LNH-reduced count fits `max_candidates` is therefore always fully enumerated (never truncated mid-search), and a size that doesn't fit is skipped in O(1) — exactly as cheaply as the plain, pre-symmetry-breaking analytic skip always was, even for a signature with few or no named constants, where LNH cannot reduce anything (functions and predicates stay fully exhaustive regardless of the flag). `semantics.secondorder`'s `_so_structures` inherits the LNH generator by swapping its one enumeration call, with no new parameter of its own; its pre-flight still uses the plain (non-LNH-aware) analytic count, matching the roadmap's "reuse, not a separate implementation" scope for that module. Free variables, MSFOL (sorted) search, and the numeral-as-constant reading `semantics.tarski` already established are all unaffected either way.

### `semantics.fuzzy_kripke` — graded Kripke semantics: a truth-degree evaluator for modal logic

A new module, `FuzzyKripkeModel` / `satisfies_fuzzy_modal`, generalises `semantics.kripke`'s two-valued possible-worlds evaluator the way `fuzzy_evaluate` generalises classical FOL: each named accessibility relation carries an edge WEIGHT in `[0, 1]` instead of a crisp edge set (a missing edge reads as `0.0`), each world's valuation carries an atom DEGREE in `[0, 1]` instead of a crisp atom set, and `satisfies_fuzzy_modal` returns a truth degree, not a bool. `Box` is the residuated universal reading `inf_w' tnorm.impl(R(w,w'), deg(phi,w'))` and `Diamond` the t-norm existential reading `sup_w' tnorm.conj(R(w,w'), deg(phi,w'))` — the residuated-Box/t-norm-Diamond pair from Fitting's many-valued modal logic and Bou-Esteva-Godo-Rodriguez's minimum many-valued modal logic over a finite residuated lattice; `Knows`/`Believes`/`Says`/`Wants` get the same residuated-universal reading for free over their own agent-keyed relation, via the identical relation-name convention `semantics.kripke` already documents. The aggregation domain at each world is that world's true successors under the named relation, unioned with the declared world set (matching `KripkeModel.successors`, which is never filtered by the declared world set either) — so a relation edge to a world outside the model's declared `worlds=` set is still counted correctly, not silently dropped. The three t-norms in `tnorm.py` (Lukasiewicz, Godel, product) are reused unmodified. v1 is deliberately narrow, matching `kripke.py`'s own propositional/ground v1 discipline: exactly graded Box/Diamond/Knows/Believes/Says/Wants with single-step aggregation and no fixpoints. Every other node kind — classical crisp connectives, quantifiers, lambda terms, temporal closure, hybrid logic, public announcement logic, group-epistemic E/D/C, and deontic serial-frame reasoning — is refused by name with a NotImplementedError/TypeError naming the construct, never silently approximated, since a graded fixpoint or model update over a continuous t-norm is an open research question in its own right. On edge weights and atom degrees restricted to `{0.0, 1.0}`, the new evaluator agrees exactly with `satisfies_modal` on the structurally matching crisp formula, for every t-norm, over thousands of random frames (including frames with relation edges to worlds outside the declared world set); the residuated duality (Diamond phi = Not Box Not phi) holds exactly under Lukasiewicz's involutive negation and is shown to fail under Godel's non-involutive one.

### `eval.datasets.proofwriter` — `check_gold_proof`: verifying ProofWriter's own gold derivations against the kit's forward-chaining fixpoint

`load_proofwriter_structured`'s generated FOL had no independent check that it actually proves what ProofWriter's own dataset says it proves — `solve_structured_example` decides a question against its OWA label, but never against the dataset's own step-by-step justification. `check_gold_proof(example)` closes that gap: a new private grammar module, `eval.datasets._proofwriter_proof`, parses `question["proofs"]`'s two annotation shapes (a `Leaf`/`Apply`/`Or` derivation forest over the theory's own named `tripleN`/`ruleN` references, or — for `"Unknown"` answers — a `FailWitness` walk-back chain of candidate rules abandoned because their own body could not be decided), and `check_gold_proof` cross-checks the parsed annotation against `_closed_model(record_provenance=True)`, the SAME forward-chaining fixpoint `solve_structured_example` already uses internally, run a second, independent time with provenance recording turned on. A derivation is confirmed by checking that the target atom's provenance names the exact chain of facts/rules the annotation cites (`_match_gold_derivation`); a fail witness is confirmed by checking that the target atom is genuinely absent from the fixpoint's derived atoms, and — when the witness names its first candidate rule — that rule's own grounding has an unsatisfied body in the completed perfect model (`_rule_body_holds`). Measured against 4550 checkable real questions fetched from `hitachi-nlp/proofwriter_processed_OWA`, 4543 agree (99.85%); the remaining 7 (0.15%) are a documented, narrow ambiguity where a rule's `"~"` (negation-as-failure) condition is genuinely undetermined under ProofWriter's own open-world reading rather than absent-under-closed-world, so `_closed_model`'s NAF-as-absence semantics lets a rule fire that the OWA-consistent annotation says should not — `check_gold_proof` correctly reports these as `ok=False` rather than silently agreeing, the intended behaviour rather than a checker defect.

`_rule_body_holds`, the private helper `check_gold_proof` uses to decide whether a fail witness's first candidate rule could have concluded the target atom, checks EVERY grounding of that rule sharing the target's head atom rather than returning on the first one `itertools.product` happens to visit, so a non-firing grounding can never mask a later, genuinely firing one in the diagnostic `rule_body_holds` field — the fixpoint's own `derivable` verdict (independently computed from the full provenance dict) is unaffected either way, only the explanatory field alongside it.

### `↓`, the state-variable binder — full hybrid logic H(@,↓), honestly bounded

Hybrid logic H(@) (nominals, `@i φ`) was decidable and complete: `hybrid_is_valid` could safely collapse "not proved" into "refuted" because Z3 reliably closes every instance. Adding `↓x.φ` ("name the current world `x`, then continue" — `Down` in `fol._hybrid_nodes`, parsed at the same grammar level as `∀`/`∃`) buys real expressive power a fixed nominal assignment cannot: `↓x.□¬x` states irreflexivity of the *current* world as one formula, `↓x.□x` reflexivity. It also makes validity UNDECIDABLE — so nothing here pretends otherwise. `standard_translation` now threads a `↓`-bound name to the current-world term (no fresh quantifier; this is what "bounded fragment" means), which is what makes the new `fol.modal_translation.down_is_valid` possible: a Z3 `Solver()` called directly rather than through the bare-bool `is_valid` wrapper, so it can honestly report PROVED (a real proof, sound unconditionally) or UNKNOWN — and, by design, NEVER REFUTED, since turning an arbitrary Z3 model back into a presentable finite Kripke countermodel is real work this route sidesteps on purpose. `atp.kripke_enum.KripkeEnumBackend` already decides `↓` REFUTED, unmodified — its bounded finite-model search calls `satisfies_modal`, which now has one new case (`Down` locally rebinds a nominal to the current world, then recurses — no alpha-renaming machinery needed, since the rebinding is a plain environment override that already gets shadowing and no-capture right by construction) — and every countermodel it returns is independently re-verified. `atp.hybrid_down.down_decide` runs both halves and returns whichever one settles the question. Every route that can only stay sound by staying inside a decidable fragment — `hybrid_is_valid`, the modal tableau's five entry points, `fol.qml`, and the HOL/THF shallow embeddings (`hol.isabelle_modal`, `hol.thf_modal`, `hol.ho_modal`) — now refuses a `↓`-formula BY NAME instead of silently answering for a logic bigger than the one it was built for.

`Down`, `down_is_valid` and `down_decide` are exported from `unicode_fol_kit.fol` / `unicode_fol_kit.atp` / the top-level package alongside `Nominal`/`At`. `api.prove(..., logic="hybrid")` decides ↓-formulas too: its `HybridBackend` goes through the same bounded standard translation, so a Z3 `unsat` is a proof and a Z3 `sat` a genuine countermodel of the translation, hence of the formula — checked against brute force over every frame with up to three worlds; a timeout stays UNKNOWN. `down_is_valid` keeps its narrower, PROVED-only contract.

### `hol.deepshallow.qml` — Tier 2 of the deep/shallow stack: a genuinely quantified embedding, K frame + constant domain only

The four Tier 1 logics deep-embedded in `hol.deepshallow` (propositional modal K, intuitionistic, Lewis-conditional, relevant B) are all binder-free, so their faithfulness proofs are a one-line `induct f arbitrary: x`. `hol.deepshallow.qml` is the first quantified member of the family: object variables are de Bruijn-indexed (`obj = BVar nat | FVar s`, prepending one entry to an explicit assignment stack `env = nat ⇒ i` under `∀`/`∃` via Isabelle's own `case_nat`), so `truthD` needs no capture-avoiding substitution and every faithfulness theorem (`faithful1a/1b`, `faithful2/3`, `sound_min`) is STILL a one-line proof — the only change from Tier 1 is generalizing that assignment stack too (`induct f arbitrary: e x`), confirmed against a real local Isabelle build (~2s, no sledgehammer, no sorry/oops). Deliberately scoped to make the mechanization tractable rather than attempted in full generality: base frame K (`R` left arbitrary, as in `hol.deepshallow.modal`), the CONSTANT domain regime only (one set `D` shared by every world, structural in the TYPES rather than a runtime `mode=` choice), and alethic `□`/`◇` only — every other frame, domain regime, agent-indexed/temporal/deontic operator, equality and function term is refused by name (`NotImplementedError`), with `hol.isabelle_modal` / `hol.thf_modal` pointed at for those. `qml_to_deep(formula, atoms, consts)` encodes a formula: `atoms` collects predicate symbols exactly like the Tier 1 encoders; `consts` — a second, REQUIRED `AtomConsts` resolver, with no silent auto-create — collects object constants. Share its de-collision pool with `atoms`'s the way `qml_deep_faithfulness_theory` itself does (`consts._used = atoms._used`) so a predicate and a constant that sanitise alike never collide on the one Isabelle type `s` both use, and emit BOTH `atoms.decls()` and `consts.decls()` in any hand-assembled theory. `qml_deep_faithfulness_theory` emits the full theory, optionally grounded in a concrete formula. Verified against three independent routes on a curated battery — the Barcan formula and its converse (valid under a constant domain), `∀x□A(x)→□∀xA(x)` / `□∀xA(x)→∀x□A(x)` (both valid here, though the first flips to invalid under a varying domain — checked directly against `qml_is_valid(mode="varying")`), a K-invalid `◇P→□P`, a quantifier-under-dead-end invalidity, and a ground formula naming a constant: `fol.qml.qml_is_valid` (Z3, constant domain, frame K), a brute-force scan of `semantics.kripke.satisfies_modal` over every small (1-2 worlds, 1-2 objects) constant-domain K model, and — live-Isabelle-gated — `check_theory` on the emitted theory, both ungrounded and grounded in several of the battery formulas (and on a hand-assembled theory built entirely from the caller-facing `atoms`/`consts` pattern), none of which contains `sorry` or `oops`.

`consts` was a silently-defaulted, auto-created resolver in an earlier draft of this module: a caller who built a hand-assembled theory the documented way (emit `atoms.decls()`, call `qml_to_deep` without a `consts` of its own) got an ill-typed Isabelle theory three steps downstream, with an unreachable set of object-constant declarations and a kernel error ("Extra variables on rhs") rather than a Python-level signal at the call site. Caught and fixed before release: `consts` is now a REQUIRED argument, so the same mistake is a loud `TypeError` where the formula is built, not a cryptic kernel failure where it is checked, and the docstring states the required pool-sharing pattern explicitly. Refusal coverage was also widened with dedicated tests for the deontic, hybrid, and many-sorted node kinds the encoder's catch-all already rejected but nothing exercised by name.

### `prob.nilsson` / `prob._column_gen` — a second, column-generation route past `max_atoms`

`entailment_bounds`'s only algorithm materialised one Z3 `Real` per possible world (`2^n` for `n` distinct atoms) — exact, but explicitly bounded by `max_atoms` because that blow-up is real. A new `strategy` keyword adds `"column_generation"` (`prob._column_gen`; the default `"direct"` is byte-for-byte unchanged) — the IDENTICAL linear program, decided without ever building that array. A small `columns` subset of worlds grows on demand, one world at a time, chosen by an EXPLICIT dual LP (Z3's `Optimize` exposes no shadow-price/dual accessor — verified directly, `dir(z3.Optimize())` has none — so the dual is derived by hand and solved as its own small `z3.Optimize` call) paired with a pricing subproblem that searches all `2^n` worlds AT ONCE via a Z3 Boolean-SAT query over the `n` atoms, never an enumeration of them. Feasibility is found the same way, through a standard two-phase artificial-variable construction, so a genuinely probabilistically-inconsistent constraint set is refused with the LITERALLY IDENTICAL `ValueError` message either strategy raises (both now build it through one shared helper). The termination/optimality argument — LP weak-plus-strong duality applied to the restricted master's own dual, the classical column-generation correctness proof — is written out in full in `_column_gen`'s module docstring, and the test suite checks it two ways: exact `Fraction` equality (never a tolerance) against `strategy="direct"` on a large hand-checked, seeded-random, and literature (Nilsson 1986) battery including conditional, vacuous, degenerate, and empty-constraint-set cases; and, past `max_atoms` where `"direct"` can no longer itself serve as an oracle (a 45-atom clustered case), against the classical Fréchet/Bonferroni closed form for an intersection of fixed-marginal events, together with an independent from-scratch re-verification that the solver's own reported witness distribution actually attains the returned bound. `max_atoms` is not enforced under `"column_generation"` at all (the whole point); its own brake is a new `max_columns` (500 by default), which raises `ValueError` rather than ever returning an unproven bound. Every existing `entailment_bounds` call — and its default strategy — is unaffected.

The phase-1 artificial-sum objective at one of the module's four `z3.Sum` call sites was missing the guard the other three already carried against `z3.Sum([])` — a plain Python `0`, not a z3 AST node, the moment a restricted master ever had zero LP rows (a legitimate case: an empty constraint set). `opt.minimize(0)` then failed with a raw `AttributeError` inside z3's own binding rather than any answer from this module. Fixed with the same guard already used elsewhere in the file (`z3.Sum(s) if s else z3.RealVal(0)`), confirmed to return the same `Fraction(0,1)`–`Fraction(1,1)` bounds `strategy="direct"` already gave that input, and pinned by a regression test parametrized over both strategies.

### `atp.tstp` — the write side: certified resolution derivations out as annotated TSTP text

`atp.tstp.parse_tstp_derivation` only ever read a prover's TSTP proof text; `to_tstp(derivation, *, name_map=None)` is the write-side companion, turning a `ResolutionStep`/`ResolutionDerivation` the kit has already CERTIFIED via `atp.resolution_check.verify_resolution_proof` into the same annotated `cnf(name, plain, clause, inference(rule, [status(thm)], [parents])).` text that function reads. An `"input"` step (0 parents) carries no `inference(...)` source at all, matching how the reader treats a leaf statement; every other rule is mapped onto a TSTP token `atp.tstp_check`'s own checked-rule tables actually dispatch to a matching independent re-derivation, not merely a plausible-looking name — `resolve`→`resolution`, `factor`→`factoring`, `paramodulate`→`superposition` (not the more obvious `"paramodulation"`, which that module does not register at all), `demodulate`→`rw`, `reflexivity`→`equality_resolution` (not `"eq_resolution"`, likewise unregistered) — so a rendered proof comes back genuinely `verified` under `check_tstp_derivation`, not merely parseable. Symbol names are sanitised through the same `atp._tptp_problem._sanitize_for_tptp`/`TptpNameMap` machinery `generate_tptp_problem_with_mapping` uses for a TPTP problem file, with an optional pre-built `name_map` so a derivation over a problem already exported that way reuses identical spellings. Two distinct kit-level names that would render as the same TPTP identifier are refused with the same `NotImplementedError` that guards a problem export. A derivation `verify_resolution_proof` does not certify is refused before any text is written at all.

A round-trip hole was found and closed before this shipped: `Node.to_tptp` folds only a symbol's first character on export while the TSTP reader's own case handling is asymmetric on import (a predicate's first letter is always re-capitalised; a constant/function's case is never touched at all), so a lower-case predicate like `bar` or an upper-case-initial constant like `Foo` previously passed through `to_tstp` as an untouched "already legal" identity and came back under a silently different kit-level name — reproduced directly, fixed by routing any name that is legal TPTP syntax but the wrong case for its namespace through the same de-collided synthesis path an illegal name already used, and re-verified through a full `parse_tstp_derivation` + `apply_reverse_tptp` round trip. A second, narrower gap survived that fix alone: the collision check only ever saw the derivation's own sanitised literals, never a caller-reused `name_map`'s tokens for names the derivation does not itself repeat, so two distinct original symbols could still render to the identical TSTP token undetected. Closed by widening the check to run over synthetic sentinel nodes built from the full (possibly caller-supplied, possibly extended) `name_map` as well as the derivation's own literals.

### `fol.prover9_input` — applying newly-declared `op(...)` operators, not just skipping them

`parse_prover9_problem`/`load_prover9` used to recognise a Prover9 `op(precedence, type, symbol)` directive and silently skip it — any formula written using the declared operator's own infix/prefix syntax then failed with a raw Lark grammar dump, not a targeted diagnostic. `op(...)` directives are now applied: a genuinely new symbol at a term-tier precedence (below Prover9's own arithmetic tier, 500) becomes a `Function`-producing operator spliced next to the term grammar's atomic level; one at an atom-tier precedence (500-750, excluding the comparison tier at 700) becomes an `Atom`-producing operator spliced next to the existing comparisons. `infix`/`infix_left`/`infix_right` (Prover9's own `xfx`/`yfx`/`xfy`) chain — or, for plain `infix`, deliberately do NOT chain without parentheses, reproducing Prover9's own non-associative semantics for free, since the grammar rule a plain `infix` declaration splices in has no self-recursive branch; `prefix`/`prefix_paren`/`postfix`/`postfix_paren` splice in at the term tier. A per-file Lark grammar+transformer pair is built and cached by the exact tuple of active declarations, so a file with no custom operators — the common case — still runs on the original shared singleton parser, unrebuilt and unslowed. Any identifier-shaped symbol is supported regardless of case, since the generated internal grammar rules are named from a numeric index, never from the symbol itself.

Two things are refused loudly, by name, as `Prover9ParsingError`, regardless of whether the declared operator is ever used, because applying them could silently change the meaning of other, unrelated text already in the file: redeclaring an existing built-in (the manual's own default operator table, hard-coded and cited for this), and redeclaring a symbol the same file already gave a custom meaning to. A malformed directive (wrong arity, a non-integer precedence, an unknown type keyword, an unsupported symbol) is refused the same way. Everything else syntactically well-formed but outside the two splice windows is accepted but left harmlessly inert, exactly matching every `op(...)` directive's behaviour before this feature existed.

There is no live Prover9 binary in this dev environment, so every placement and refusal claim is verified against a tree worked out by hand with standard precedence climbing over the manual's own default operator table, cross-checked on the atom-tier and term-tier cases by the kit's own Z3-backed `is_valid` as an independent second route. Two of those differentials — an atom-tier and a term-tier operator, each checked against a plain Z3 tautology built from `expected` alone — were content-blind by construction (true for any predicate/term, not just the parsed one) and were replaced with independently hand-built quantified/functional axioms that only entail the check goal when `expected`'s own predicate name, argument order, and function nesting are exactly right; each new differential was confirmed to fail against a deliberately-broken substitute (an unrelated predicate, swapped operands, the wrong function nesting) before being accepted.

### `fol.signature`, `fol.casl_export`, `eval.predicate_match` — arity/name-clash bookkeeping shared, the accumulation and resolution policy stays per-consumer

`Signature.from_formulas`, `casl_export._analyze`, and `predicate_match`'s symbol-inventory walk each independently classified a formula's vocabulary; two narrow, genuinely-duplicated pieces of that are now shared, not three copies of one idea — `casl_export`'s per-argument-position sort inference (its own union-find, with its `default_sort` total-resolution policy) stays exactly where it is, since it is incompatible with `Signature.validate`'s None-never-conflicts policy by design, not by neglect. First, the new `fol.signature.inventory_of(node)` is the LENIENT counterpart of `Signature.from_formulas`'s classification walk: it never raises, keeping every conflicting `(name, arity)` pair and every constant-vs-function name clash side by side instead of refusing — exactly what scoring possibly-malformed model output needs. `eval.predicate_match._symbol_inventory` is now a genuine alias for it (checked by object identity in both modules' test suites), not a second, independently-written `node.walk()` pass. Second, the arity-conflict and constant/function name-clash REFUSAL itself — the comparison-and-raise, not how each caller accumulates the values compared — is factored into `fol.signature._check_single_valued`/`_check_not_dual_use`, called by both `Signature.from_formulas` and `casl_export._analyze`. Each caller keeps its own accumulation policy and message wording: `from_formulas` collects every arity a symbol is used at across the whole batch before reporting, naming all of them, while `casl_export._analyze` checks incrementally, per AST occurrence, against a running single recorded value, so it can raise — and short-circuit the shared sort-inference union-find walk — the moment a conflict first appears; a three-way arity conflict is therefore still reported differently by the two, a documented, pre-existing difference in accumulation policy rather than something the sharing was meant to erase. Every existing `align_symbols`/`match_predicates`/`casl_export`/`Signature.from_formulas` test case and refusal message is byte-identical before and after the swap, verified by a differential capture run against the whole existing suite plus new adversarial cases (an arity-inconsistent predicate, a name used as both a constant and a function, and a predicate/function pair sharing one name) that `inventory_of` never raises on.

### `hets.owl_backend` — a second, independent external OWL 2 DL reasoner, over Hets/FaCT++

A Docker capability spike (full REST calls/responses recorded in `hets/owl_backend.py`'s own module docstring, and folded back into `hets/docker.py`'s "Container image quirks" section) found that the `spechub2/hets` image DOES parse OWL 2 and DOES bundle a genuine, working DL reasoner: `Fact` (FaCT++ 1.6.3, LGPL-2.1), reachable via `POST /consistency-check` with `reasoner="Fact"` passed explicitly — an unset reasoner picks a broken `OWL22CASL->SoftFOL` translation for OWL input and crashes outright on an ontology as simple as one class asserted a subclass of `owl:Nothing`. Neither Pellet nor HermiT is offered by this image at all, so the roadmap's conditional AGPL callout does not apply. `unicode_fol_kit.hets.owl_backend` wires this up as a second, independent oracle alongside `dl.owl_reasoner` (HermiT via owlready2, in-process): it renders the kit's `TBox`/`ABox`/`Concept` AST to a small, self-contained OWL 2 Functional-Style Syntax document (fresh synthetic `:C<n>`/`:R<n>`/`:I<n>` names, never the kit's own name strings verbatim), uploads it via the existing `HetsClient`, and mirrors `dl.owl_reasoner`'s function-per-namesake shape exactly (`external_concept_satisfiable`, `external_subsumes`, `external_abox_consistent`, `external_instance_check`/`_retrieval`, `external_realize`/`_all`, `external_equivalent`) over the SAME ALCHQ + I + O fragment. A 38-test battery (`hets_live`-gated for the live half) agrees exactly with `dl.tableau` on the ALCHQ fragment and with `dl.owl_reasoner` on inverse roles and nominals, and additionally turned up a latent, unrelated bug in `dl.owl_reasoner` itself (a genuine atomic-to-atomic TBox equivalence crashes it with a raw owlready2 `TypeError`, since it models `⊑` as literal Python class inheritance) — filed separately, not fixed here, out of this change's scope. Never in a default chain and never starts a Docker container itself, exactly like `atp.hets_backend` and `dl.owl_reasoner`.

### `fol.qml`, `hets.dol` — the standard translation reaches CASL/DOL/Hets

CASL/DOL have no modal operators of their own, and building a native `logic Modal` institution would have been strictly NARROWER than what already existed unofficially: `fol.qml`'s first-order standard translation already lowers the kit's full modal fragment (alethic/temporal/deontic/per-agent epistemic-doxastic/PAL) to exactly the classical fragment `fol.casl_export` accepts, and three OTHER independent modal cross-checks (nanoCoP-M, LEO-III, Isabelle) already exist — so this promotes that existing, unofficial composition into tested public API instead of building anything new. `fol.qml.qml_validity_formula` is the new documented entry point onto the closed classical-FOL Node `qml_is_valid` already builds and feeds to Z3 (a literal delegation to the unchanged, private `_validity_formula` — every existing positional call, including `atp.resolution`'s, is untouched). `hets.dol.to_dol_library_from_modal` composes that translation with an injective identifier-sanitising rename (`qml`'s own auto-generated fresh names — the world variable `_w0` `_Fresh` mints, the Geach axiom's `_gz0`/`_gw`/`_gu`/`_gv`/`_gt` — are not legal CASL identifiers; the sanitiser fixes exactly that and nothing else, via a two-pass seed-then-dedupe algorithm that leaves every already-legal name untouched even under a genuine collision, e.g. a user's own object variable also literally named `w0`), an aliasing of any world-relativized `=`/`≠` atom the translation produces (qml's `_st` appends the current-world argument to EVERY atom it visits, `=`/`≠` included, so a genuinely binary user atom comes out non-2-ary — not CASL's own fixed, rigid, always-binary identity at all; the bridge renames it to a fresh, uninterpreted predicate `weq`/`wneq`, the SAME non-rigid reading `qml_is_valid`'s own Z3 check, the Kripke model checker, and the Isabelle/THF modal exporters already give an object-language equality inside a modal context — a genuinely 2-ary `=`, e.g. a world identity internal to the translation's own frame axioms, is left exactly as CASL's native `=`), and the EXISTING, unmodified `fol.casl_export.to_casl_spec` / `hets.dol.to_dol_library`, into one uploadable `.dol` library. A battery of known modal theorems and non-theorems — T/S4/S5 axioms on their characteristic frames, a Geach frame, Barcan/converse-Barcan under all four domain regimes, a quantified non-theorem, many-sorted input, the `_w0`-vs-`w0` collision case, and a world-relativized `=`/`≠` atom under a box — is cross-checked live against a real Hets server (SPASS) and agrees with `qml_is_valid`'s own Z3 verdict on all 25 cases (an `Open`/unknown Hets result is never counted as agreement or refutation); the propositional slice of the same battery additionally agrees with `atp.modal_tableau`, a third independently-implemented route, wherever a propositional tableau can even express the query (it has no rules for quantifiers or Geach frames, so the Barcan/sorted/Geach cases are outside its reach by design, but the equality/inequality cases ARE within its reach and agree too). `fol.casl_export`'s own docstring is updated to point at this bridge instead of describing it as unaddressed future work — no change to that module's own fragment gate, sort inference, or rendering logic, including its own exactly-2-ary `=` check, which a modal-bridge caller now never even reaches for an equality atom.

A genuinely 2-ary `≠` atom reaching the sanitiser — reachable only by calling `hets.dol.sanitize_modal_identifiers` directly on a hand-built formula, bypassing `to_dol_library_from_modal`'s documented pipeline, since `qml`'s own `_st` world-relativization always widens `≠` to 3-ary or more — is now refused loudly with `NotImplementedError` naming `≠`, instead of falling through to the ordinary predicate-renaming path: CASL has a rigid 2-ary fallback for `=` but no native disequality connective at any arity, so silently renaming it to an arbitrary legal identifier would lose every trace that it denoted inequality. This mirrors, one layer earlier, the refusal `fol.casl_export.to_casl_spec` already gives the same atom when handed directly.

### `hol.lean` — a first Lean 4 export: classical FOL/MSFOL and propositional modal K, emit-only plus an opt-in live elaboration tier

`unicode_fol_kit.hol.lean` is the Lean 4 counterpart of `hol.classical`'s THF/Isabelle pair — a first vertical slice, not yet parity (no relevant/substructural/many-valued/second-third-order/deepshallow Lean routes; those stay separate follow-ons once this pattern is proven). `to_lean_fol`/`to_lean_msfol` emit classical FOL/MSFOL exactly like the existing THF/Isabelle exporters, reusing their `_SymbolResolver`/`_free_variables`/`_reduce_nl_nodes` machinery directly (the signature inference is shared code, not reimplemented), and `to_lean_modal_k` emits a Benzmueller-style shallow Kripke embedding of the propositional modal-K fragment (Box/Diamond + connectives over ground atoms, frame K, no conditions on the accessibility relation). The one real semantic trap a bare Lean `axiom Ind : Type` has that Isabelle's `typedecl` does not — non-emptiness is not automatic — is closed explicitly: every emitted theory declares `axiom Ind_nonempty : Nonempty Ind` and registers it as a type-class `instance`, hand-verified against a real toolchain with `(forall x, P x) -> (exists x, P x)` (only provable because of that witness); the modal-K embedding makes the same commitment for its Kripke world type. Equality stays the uninterpreted `feq`/`fneq` pair by default (`native_equality=True` opts into Lean's own `=`/`neq`), matching the toolkit-wide HOL convention.

An optional live tier (`find_lean`/`lean_available`, discovering a toolchain via `UFK_LEAN_HOME`/`PATH`/the standard `elan` install dir `~/.elan/bin`, and `check_theory`, which runs bare `lean` on the emitted file — no Mathlib, no `lakefile`, needed for either fragment) turns *emit* into *elaborated*, and for a hand-written proof, *kernel-checked* — `LeanBuildResult.proved` is `True` only when the build exits 0 AND no `sorry` warning fired, so a file this module presents as checked is never quietly not. The modal-K encoding is validated two ways against the kit's own labelled modal tableau (`atp.tableau.is_valid_tableau`, already separately tested): the K axiom elaborates with a hand-written, kernel-checked proof, and the T axiom (not a theorem of K) is refuted, not merely left unproved — a concrete, two-world, decidable instantiation makes Lean's own `decide` tactic positively report the goal is false. `lean_decide_fol`/`lean_decide_modal_k` add a small, honest tactic battery (`decide`/`tauto`/`aesop`) returning `VALID`/`UNKNOWN` only (no countermodel search, so no `INVALID`); `tauto`/`aesop` are Mathlib tactics the kit deliberately does not install, so without it they fail to parse and the battery just moves on — never a crash, never a false `VALID`. New pytest marker `lean_live` gates every live test, skipped automatically without a toolchain, exactly like `isabelle_live`/`hets_live`/`owl_live`. New guide page: `docs/guide/lean.md`.

Every emitted identifier (predicate, function, constant, bound variable, and the modal encoding's Kripke-world binders) is de-collided against Lean 4's reserved words and this module's own scaffold names by a single global-uniqueness pass keyed on each symbol's LOGICAL identity, not its rendered string — so two independently-sanitised symbols that happen to produce the same candidate string (e.g. a predicate and a bound variable both named `Foo`, or a ground atom named `w0` colliding with a Kripke-world binder token) are still guaranteed distinct emitted identifiers rather than one silently shadowing the other.

### `eval.exercise_gen`, `semantics.modelfinder` — constructively-generated exercises, and an honesty helper for a skipped model size

`eval.exercise_gen` is new teaching infrastructure, not an evaluator: everything else in `eval` scores a formula an LLM or a student already produced; this module manufactures the exercise itself, with no LLM involved anywhere. Three generators, each narrower than the roadmap draft's original framing, to avoid a claim this kit's own bounded search procedures cannot honestly support (see the module's own docstring for the argument on each): `generate_valid_invalid_pair(signature, max_atoms, seed)` samples a quantifier-free formula over 0-ary predicates and classifies it with `semantics.truthtable` — complete for that fragment, so "valid" is never a guess — with a deterministic fallback construction (`phi -> phi`; `atom & !atom`) guaranteeing every call terminates even on the rare sample that misses naturally. `generate_entailment_with_proof(signature, target_depth, seed)` does not search for a proof and then measure its depth — `atp.fitch_search.find_fitch_proof`'s own docstring already disclaims that "no proof at depth d-1" could ever certify minimality — so it instead assembles a chain of nested `->I` boxes bottom-up with `atp.fitch`'s `Proof`/`Subproof`/`Line` primitives to EXACTLY the requested depth and re-checks the result with `verify_proof` ("soundness is free", per that module's own docstring). `generate_theory_with_model_size(signature, target_size, seed)` samples a strict total order over one binary relation from `signature`, forced by a chain constraint to contain at least `target_size` pairwise distinct elements — the textbook "an irreflexive total order needs domain size >= 2" fact, generalised to an arbitrary chain length — and confirms both that a model of exactly that size exists and that none smaller does.

That last confirmation needed a new `semantics.modelfinder.is_size_exhaustive(formulas, k, max_candidates, symmetry_breaking)` helper first: `find_model` conflates "this size was searched and refuted" with "this size was SKIPPED because its interpretation space exceeded `max_candidates`" — both come back as the same `None`, so a "minimal model size N" claim built on `find_model` alone could be silently wrong on a signature with a few more predicates or a higher arity than this module defaults to. `is_size_exhaustive` mirrors `find_model`'s own pre-flight candidate-count check (the raw count, or the LNH-reduced one under `symmetry_breaking=True`, matching exactly which branch `find_model` itself would take for a sorted vs. unsorted theory) without running the search, so `generate_theory_with_model_size` checks every size below its target first and refuses loudly (`ValueError`, never a silently narrower claim) the moment one of them would only have been skipped. A binary relation's interpretation count grows as `2**(k*k)` even under symmetry breaking (only CONSTANT assignments are LNH-reduced; function and predicate tables stay fully exhaustive either way), so this refusal is reached well before `target_size` passes 4 under the default `MAX_CANDIDATES` budget — deliberate, not a bug.

Every generator's answer key is re-verified by an independent route before it is returned (a fresh truth-table classification plus a fresh `tarski.models` countermodel check; a fresh `verify_proof` pass; a fresh `find_model`/`is_size_exhaustive` pair), and the test suite goes one step further, checking each against a route that shares no code with either the generator or the primitive it calls: a from-scratch `2**n` valuation enumeration and evaluator for the pairs, a from-scratch nested-`Subproof` depth counter calibrated against hand-built LEM/De Morgan derivations for the proofs, and a dumb brute-force enumeration of every structure below the target size plus a Z3 "exactly k elements" satisfiability check for the theories. Every generator is seeded and reproducible: the same seed always produces a byte-identical exercise (note: for `ModelSizeExercise`, "byte-identical" describes content, not `==` — its `witness` field is a `semantics.tarski.Structure`, which has no `__eq__`, so compare `witness.domain`/`witness.predicates` etc. field-by-field, not the whole object; see the module's own docstring).

### `atp.tptp_ncl`, `fol.qmltp_input` — NXF's native quantified fragment, the D frame, and a QMLTP problem reader cross-checked against 60 of its own recorded verdicts

`atp.tptp_ncl.to_tptp_ncl` covered only the mono-modal alethic PROPOSITIONAL fragment (0-ary atoms, K/T/S4/S5) — a quantified formula or a non-nullary atom raised `NotImplementedError` by name. Both are now supported: `Quantifier`/`SortedQuantifier` render as NXF's own native `! [X: <sort>] : (...)` / `? [X: <sort>] : (...)` (TPTP's built-in `$i` for an untyped quantifier, a fresh `tff(<sort>_type,type, <sort>: $tType ).` per user sort), and `Atom` of any arity is accepted, with a `tff(<name>_decl,type, ...)` declaration per distinct sort/constant/predicate the formula actually uses — verified, construct by construct, against real NXF translations of the very QMLTP problems this release's reader also bundles, not guessed from the specification paper's grammar alone. Two symbols that would collide under NXF's identifier folding — same token, different type, or a sort/constant/predicate sharing one name — are refused rather than silently aliased, generalising a check the propositional fragment already had; this now genuinely covers sorts too, closing a gap where two distinct sort names differing only in case (e.g. `Human`/`human`) silently collapsed into one shared `$tType` declaration instead of being refused. `frame="D"` (serial K, i.e. KD) is new, mapped to the confirmed real token `$modal_system_D`. A compound function-term argument is refused by name: no genuine NXF function-symbol type declaration was found anywhere in the checked corpus (only predicates and free constants), so its exact shape is not confirmed and is not guessed at. Two further soundness gaps are closed in this same release: an equality/disequality atom (`=`/`≠`) now requires both operands to compute to the SAME NXF sort — native TFF's polymorphic `=` has no subtyping/coercion, unlike the kit's own guard-predicate-based `SortedQuantifier` semantics, so a mismatch is refused by name rather than silently emitting a type-incorrect `tff` problem; and the arithmetic comparison predicates (`<`/`>`/`≤`/`≥`) plus a bare `Number` literal anywhere in the formula are now refused by name too, instead of applying `$greater`/`$less`/... to `$i`-typed operands or defaulting a numeral to `$i` — both need one of TPTP's own arithmetic sorts (`$int`/`$rat`/`$real`), which this exporter still does not declare, mirroring `atp.tptp_tff`'s identical, already-tested TF0-only refusal of the same two constructs rather than inventing a new policy here.

A third soundness gap is closed in this pass: a genuinely FREE (unbound) `Variable` used anywhere in the formula — e.g. an `Atom`/equality argument with no enclosing `Quantifier`/`SortedQuantifier` — used to default silently to sort `$i`, emitting an NXF conjecture with a real free variable and no binder or declaration; TPTP reads a free variable in a conjecture role as EXISTENTIALLY quantified (not universally, the reading a caller who forgot a binder would plausibly intend), so this silently changed the exported problem's meaning. Now refused by name instead. Separately, this pass caught and reverted a REGRESSION from an earlier draft of this release: that draft had "corrected" the reflexive T-frame token from `$modal_system_T` to `$modal_system_M`, on the strength of a corpus search claim that was never actually re-run and was false — direct verification shows `$modal_system_T` is the token defined in the corpus's own canonical `Logics/LOG001_4.l` definitions file, used by the corpus's own canonical `Tooling/generateSemantics.py` generator, and used by every one of the eight canonical `ProblemBuilding/QMLTP/SemanticSpecifications/t_*.p` files, while `$modal_system_M` is never defined anywhere in the corpus and appears only inside a derived/auto-expanded subtree (`8_QMLTP`, per that directory's own README) that references a token the corpus's own canonical definitions never actually define. `frame="T"` is therefore restored to `$modal_system_T`.

`fol.qmltp_input` is a new, separate reader for the QMLTP library's OWN, older extended-`fof` syntax (Raths & Otten, TABLEAUX 2009 / CADE 2012) — a genuinely different dialect from NXF, predating it, with its own `qmf(name,role,formula).` statement keyword (not `fof`) and `#box`/`#dia` connectives, extending `fol.tptp_input`'s own Lark grammar and transformer by subclassing rather than reimplementing, so every classical connective/quantifier/atom/term rule is shared, unmodified code. A small regex scanner reads QMLTP's own per-(logic, domain-condition) `% Status` TABLE header into a `QmltpHeader`/`QmltpStatus` record. Multi-modal problems (the `tpi(...)`/`set_logic` directive and indexed `#box(name)`/`#dia(name)` connectives, the 20-problem MML domain) are refused by name, not guessed at. The reader was developed and checked against real QMLTP v1.1 problems, but no redistribution licence for the library could be found, so the kit ships none of its files: `tests/fixtures/qmltp` holds four small stand-ins written in the same syntax and header layout — the Barcan and converse-Barcan schemes, a formula that separates frame D's seriality from K, and an equality non-theorem — each with a status table derived by hand. Every one of their 60 (logic, domain) -> Theorem/Non-Theorem cells is independently decided via the existing `fol.qml.qml_is_valid` (a differential oracle sharing no code with this reader) in a parametrized regression test; there is no mismatch. `load_qmltp` reads a real QMLTP file from your own copy of the library.

### Native typed arithmetic (TFA) for Vampire/E — one numeric sort, genuinely typed

`atp.tptp_tff`'s TF0 route explicitly refuses TPTP's arithmetic sorts (`$int`/`$rat`/`$real`) — general many-sorted inference and single-sort arithmetic are different problems, and mixing them risks guessing which symbols are numeric. `generate_tff_arith_problem` (new, `atp._tff_problem`) is the arithmetic sibling instead, mirroring `atp.z3_arith.ArithEnv`'s already-proven design: the WHOLE problem lives in ONE caller-chosen numeric sort (`sort="real"|"int"`), an ordinary (non-arithmetic) predicate/function/constant is simply declared over that same sort, and `+ - * /`/`< > ≤ ≥` reuse `Node.to_tptp`'s own `$sum`/`$difference`/`$product`/`$quotient`/`$less`/`$greater`/`$lesseq`/`$greatereq` mapping verbatim — genuinely `tff`-typed this time, which is what actually lets Vampire/E switch on their native arithmetic decision procedures instead of treating those dollar-words as opaque uninterpreted symbols. `vampire_entailment` and `eprover_backend` (E, Zipperposition) gain an opt-in `sort=` option (taking priority over `tff=` when given; the default `None` leaves every existing caller's behaviour untouched byte-for-byte). Unlike the TF0 route, this one's `TptpNameMap` is a genuine, usable mapping, so a prover's own output IS reverse-mapped to original kit-level names here too. Because TFF (unlike untyped `fof`) has one flat symbol table, a predicate and a function/constant that would render as the same TPTP identifier (e.g. `Price(x)` alongside `price(x)`) is refused loudly at export time rather than emitting two conflicting type declarations for one name. Live-verified against both Vampire and E (WSL): the same `$int`-vs-`$real` divergence `atp.z3_arith` already knows about shows up identically through the external provers — `∀x (x > 0 → x ≥ 1)` is `Theorem` over `$int`, not provably `Theorem` over `$real` (a genuine counterexample, `x = 0.5`) — and a hand-picked battery of linear and nonlinear formulas with known textbook truth values never disagrees with `is_valid_arith`/`is_satisfiable_arith` in the direction that would matter (a prover's `Theorem`/`CounterSatisfiable` never contradicts the oracle; `GaveUp`/timeout stays an honest unknown).

### `mcp.server`, `comorphism` — a stated, self-enforcing STABILITY POLICY for the MCP tool surface and comorphism registry

`api.py` has carried a STABILITY POLICY paragraph for a while; the two other surfaces an MCP client actually depends on — the tool surface (names + auto-derived `input_schema`s) and the comorphism `DEFAULT_REGISTRY` (translation edges) — had none. Both now state the same shape of contract: within a minor line (0.N.x) a tool or edge is never renamed or removed, a tool's `input_schema` only ever gains new *optional* parameters (an existing parameter's name, type and required/optional flag are stable in EITHER direction), and a comorphism edge's source/target/lossy never change once registered — additions only. `docs/guide/mcp.md` gets a matching "Stability" note aimed at an MCP integrator specifically, since a JSON-RPC session has no equivalent of a `pip` version pin. Enforcement extends the self-consistency style `test_server_registers_all_thirtyseven_tools` already used for tool NAMES one level deeper: `tests/test_mcp_stability.py` hand-transcribes every tool's `(required, {parameter: type-signature})` and every comorphism edge's `(name, source, target, lossy)` from one real `list_tools()`/`DEFAULT_REGISTRY.edges()` call, then checks the pinned baseline is a SUBSET of the current registry in the allowed direction (a new tool, a new optional parameter, or a new edge never fails it) while a removal, a rename, a parameter silently turned mandatory OR silently turned optional, a parameter/edge type change, or an edge's lossy flag flipping all fail it with a named, readable diff — both directions exercised directly against small hand-built `MCPServer`/`ComorphismRegistry` fixtures, not just against today's already-clean registry.

Landed alongside it: `probability_bounds` now passes `strategy` (`"direct"`/`"column_generation"`, default `"direct"`, unchanged) and `max_columns` (500 default) through to `prob.nilsson.entailment_bounds`, so an MCP caller can reach the column-generation route that already existed underneath — both land as new optional parameters in the pinned schema baseline, `strategy` validated against the two known values with the kit's usual structured `{"error": ...}` refusal on anything else.

### `tools/mypy_ratchet.py`, CI — a ratcheted mypy gate over `unicode_fol_kit`

The package shipped `py.typed` but had no static type-check step anywhere — no mypy/ruff/flake8 config in `pyproject.toml`, no lint job in any workflow. A first real `mypy` pass surfaces several hundred pre-existing errors spread across most of the thirteen subpackages, so this is a RATCHET rather than a bare `mypy unicode_fol_kit` gate: `tools/mypy_ratchet.py` runs mypy, counts errors per file, and a new `typecheck` CI job (`.github/workflows/tests.yml`, ubuntu-latest, Python 3.11 only — a separate job from `fast` on purpose, so a type-check finding never conflates with the pytest matrix) fails only when a file's count RISES above what `tools/mypy_baseline.json` already tolerates for it; a file's count is free to drop, and a brand-new file starts at an implicit ceiling of zero so it cannot sneak in dirty. Regenerating the baseline is one documented command, `python tools/mypy_ratchet.py --update`, run identically in CI and locally — `python tools/mypy_ratchet.py` with no flags is exactly the gate CI runs.

`pyproject.toml` gains a `lint` extra pinning `mypy==2.3.1` exactly — a moving mypy version changing its own inference is a false-failure source unrelated to any code change, the same reasoning behind the E-prover/APE pins already in `tests.yml` — and a `[tool.mypy]` table (`python_version = "3.10"`, this project's floor; `packages = ["unicode_fol_kit"]`). It also sets `no_site_packages = true`: the pinned `rdkit` release ships a PEP 561 stub package whose generated `.pyi` files contain an outright syntax error (a duplicated, misordered parameter list in `Chem/rdmolfiles.pyi`), which is a BLOCKING mypy error that no per-module override can silence and which otherwise aborts the whole run before every file is even reached. Disabling site-packages discovery sidesteps the broken third-party stub, at the cost of checking every third-party call against `Any` instead of its real signature — this project's own code is held to the same standard either way.

`tests/test_mypy_gate.py` tests the ratchet's own logic (a new error, a fixed error, an unchanged count, and a renamed or removed file) against hand-written synthetic mypy output, plus one differential test against a real mypy run over a two-file scratch package (skipped when mypy is not installed) — it never runs mypy over `unicode_fol_kit` itself inside the fast suite.

## [0.27.0] - 2026-08-28

### Third order: a predicate whose argument is a predicate

Second-order syntax binds a predicate variable and then only ever APPLIES it.
Third-order syntax puts one in ARGUMENT position — `Positive(G)`,
`Essence(G, x)`, `Positive(λx. ¬G(x))` — which is a change to the argument
layer, not another binder, and is why no amount of extra quantification reaches
it. `MSFLParser(third_order=True)` parses that, and with `modal=True` on top,
third-order MODAL logic. Both are their base modes over the widened slot: the
classical one accepts exactly what `second_order` accepts plus predicate
arguments, the modal one exactly what `modal` accepts plus both, and they are
assembled by CLONING their base modes' operator registrations rather than
re-declaring forty of them that would then drift apart — pinned by a test that
compares the two operator sets outright.

The new node is `PredicateTerm`, and it is deliberately NOT a nullary `Atom`:
`Atom("G", [])` is the proposition G, `PredicateTerm("G")` is the property G,
and conflating them is exactly the type error the third order exists to make
visible. Every first-order back-end refuses it by name, as second-order
quantification already did.

**Types are inferred, across a theory rather than a formula.** Nothing in the
surface syntax says whether a slot holds an individual or a property of arity
k, and `Positive(G)` alone cannot say — but `Positive(G)` together with `G(x)`
in another axiom of the same set does. `analyse_signatures` collects the
constraints (an application fixes its head's arity, a λ-argument fixes its
slot's by binder depth, a predicate in a slot links its arity to that slot's)
and closes them under propagation, with bound predicate variables renamed apart
first so two locally-bound `P`s are never mistaken for one symbol. Two failures
are raised rather than papered over: a predicate applied at two arities, and
`MixedSlotError` for a slot used once for an individual and once for a property
(`Loves(x, y) ∧ Loves(x, G)`), which is checked at parse time. One case is
defaulted and REPORTED: a property slot no evidence reaches gets arity 1 — the
only reading on which such a formula says what it plainly means, where arity 0
would silently retype it as a predicate over propositions — and which slots
were guessed comes back in `Signatures.defaulted` and is printed as a comment
in every emitted theory.

`api.parse_any` tries the CLASSICAL third-order mode at the end of its ladder,
after `fol`, `modal` and `second_order`. It is served by the same LALR table as
`second_order`, so the only inputs it newly accepts are the ones with a
predicate really standing in an argument slot — nothing previously detected as
something else moves. The MODAL third-order mode is deliberately left off the
ladder: it inherits `modal`'s Earley table, and with a second-order binder also
available `∀ P(x)` parses there as a quantifier over the propositional atom `x`
rather than failing as the malformed quantifier every other dialect reports,
which is precisely the agreement the repair and error-routing machinery reads.

`hol.thirdorder` exports the classical case (`to_thf_to`, `to_isabelle_to`);
`hol.ho_modal` the modal one, through the shallow embedding the rest of the
package uses — propositions as functions from worlds, `mall`/`mex` polymorphic
so ONE pair of binders serves individual and property quantification and the
orders are distinguished by the type at the binder. Its lifted vocabulary is
emitted as Isabelle `abbreviation`s rather than `definition`s on purpose: an
abbreviation is unfolded by the parser, so the automation sees through the
embedding instead of having to unfold it first. Frame systems come from
`fol.frames`, so a name means here what it means on the other six routes; a
frame with no first-order condition (GL, S4.1, Grz) and every non-alethic modal
family are refused BY NAME rather than dropped, since the parser accepts `K_a`
for the same AST reason and a silently ignored operator would produce a theory
that proves something else.

### `hol.goedel` — Gödel's ontological argument, both readings, machine-checked

The argument is the standard worked example of third-order modal logic because
it cannot be stated in less, which makes it the sharpest available test of all
of the above: the axioms are written in the kit's own Unicode syntax, exported
by the kit's own emitter, and discharged by Isabelle, with nothing
special-cased anywhere.

Two variants, ONE conjunct apart — Scott's `Ess(P,x) ↔ P(x) ∧ …` against
Gödel's own `Ess(P,x) ↔ …`. Under Scott's reading the emitted theory discharges
`T1`, `C`, `T2` and `T3` (necessarily, a God-like being exists) and also `MC`,
**modal collapse**: `φ → □φ` for every proposition, the argument's best-known
and least comfortable consequence. It then runs Nitpick, which finds a genuine
model — so those theorems hold because they FOLLOW, not because the axioms
prove everything. Under Gödel's own reading the theory proves `False`: without
the `P(x)` conjunct the empty property is vacuously an essence of every
individual, and necessary existence then demands it be instantiated. The
control sits on the other side, where `Ess(P, x) → P(x)` is provable and hence
the empty property is an essence of NOTHING. Both check in about ten seconds on
a local Isabelle (`tests/test_goedel.py`, marked `isabelle_live`).

The Isar proofs are written out by hand and shipped as data; the kit emits the
theory and hands it over. Nothing searches for a proof and nothing claims a
result the caller has not run — which is also why the proofs are structured
rather than one-line automation calls: at this order the one-liners do not
finish, and a proof that takes ten minutes to not finish is not a check.

### `semantics.thirdorder` — finite models, where an argument can be a property

The counterpart of `satisfies_so` one level up, and the reason it is a separate
evaluator rather than a flag: at second order a bound predicate variable is
fully described by its ARITY, and at third order it is not. `Positive` and `G`
can both have arity 1 and mean entirely different things, because `G`'s slot
holds an individual and `Positive`'s holds a property. So `satisfies_to`
enumerates over each bound symbol's SIGNATURE — from the same
`analyse_signatures` the exporters use — and a λ in argument position is
evaluated to its EXTENSION, which is the one place a λ has a reading here.

That it is a CONSERVATIVE extension is checked rather than asserted: on a
second-order formula `satisfies_to` and `satisfies_so` return the same verdict
in every structure over a two-element domain, exhaustively, not on samples.

The cost is not where the syntax suggests. A property variable is cheap
(`2 ** n` interpretations — 32 on a five-element domain); a predicate OF
properties is `2 ** (2 ** n)`: 16 for n = 2, 256 for 3, 65 536 for 4, about
4·10⁹ for 5. `interpretation_count` gives that number without enumerating
anything and `MAX_INTERPRETATIONS` refuses past roughly a million with a clear
error rather than hanging. Beyond that, Nitpick through `check_theory` is what
finds finite models at this order — which is exactly what the Gödel consistency
check uses.

## [0.26.0] - 2026-08-25

### `fol.frames` — one modal frame table for six routes, correspondences checked

Six routes reason modally here — the standard translation (`qml`), the
labelled tableau, the finite-frame enumerator, natural deduction (`fitch`),
the hybrid translation and the higher-order embeddings — and each carried
its OWN copy of the frame table. They had drifted: the tableau knew `K45`
and `qml` did not, `qml` knew `S4.2` and `S4.3` and the tableau did not,
`fitch` and the hybrid route knew four systems between them. They now all
read `fol.frames`, which says what a system consists of, what each condition
means, and — the part that makes it checkable — which modal axiom each
condition corresponds to.

That correspondence is BRUTE-FORCED, not asserted: for every first-order
condition, over every frame on up to three worlds and every valuation, "the
axiom is valid on this frame" and "the frame satisfies the condition" must
agree (`tests/test_modal_frame_registry.py`, ~2 s). It immediately paid for
itself by correcting this repository's own note on `.3`: the exact
correspondent of the `□(□p→q) ∨ □(□q→p)` form has NO "or v = u" escape —
that weaker condition belongs to the `◇`-formulation — and the two coincide
only over reflexive frames.

New named conditions, each with its axiom: **CD** `◇p → □p` (partial
functionality), **C4** `□□p → □p` (density), **Ṁ** `□(□p→p)`
(shift-reflexivity — which is also what `◇p → ◇(p∧◇p)` corresponds to), and
**Ver** `□p` (the empty relation). New systems: `K5`, `KB`, `KTB`, `KD4`,
`KD5`, `KCD`, `KC4`, `KShift`, `Ver`, `S4.1` and `Grz`, alongside the ones
that already existed — 24 in total, and `D`/`KD` and `B`/`KTB` are now
accepted as the two spellings of one system.

The **Scott–Lemmon (Geach) family** arrives whole rather than one name at a
time: `G(m,n,r,s)` — the axiom `◇^m □^n p → □^r ◇^s p` with the condition
`∀w,u,v (wR^m u ∧ wR^r v → ∃t (uR^n t ∧ vR^s t))` — is accepted wherever a
frame name is, on every first-order route. Eight named conditions are
instances of it (reflexivity `G(0,1,0,0)`, transitivity `G(0,1,2,0)`,
symmetry `G(0,0,1,1)`, seriality `G(0,1,0,1)`, euclideanness `G(1,0,1,1)`,
directedness `G(1,1,1,1)`, CD `G(1,0,1,0)`, C4 `G(0,2,1,0)`), and a test
proves each generated schema picks the same frames as the hand-written
axiom.

Three axioms have no first-order frame condition at all — Löb (`GL`),
McKinsey (`S4.1`) and Grzegorczyk (`Grz`). They are marked as such and
carried ONLY by the higher-order routes, which assert the schema itself over
propositions; both HOL exporters gained McKinsey and Grz alongside the Löb
schema they already had. Every first-order route refuses them by name.

The refusals are the other half of the work, and one of them closed a latent
soundness hole: the finite enumerator's condition check tested the five
conditions it knew and **silently ignored any other**, so a frame class it
did not recognise would have widened to the ones it did — reporting
countermodels the named system excludes. Unknown and non-first-order
conditions now raise. The tableau likewise refuses what it has no rule for
(density, functionality, directedness, connectedness, …) instead of dropping
it, and names the route that does carry it.

New public API: `modal_axiom("5")` builds a named axiom's schema (literature
aliases included, so `W` and `Loeb`, `Q` and `C4`, `Alt1`/`Alt3` and `CD` are
one axiom each) and `UnsupportedFrameCondition`, both at top level; the
registries themselves — `FRAMES`, `FRAME_CONDITIONS`, `MODAL_AXIOMS`,
`AXIOM_ALIASES` — are reached through `unicode_fol_kit.fol`. One letter is
deliberately NOT
accepted: `M` names T in some texts and shift-reflexivity in others, so the
registry refuses it rather than picking a reading.

### `eval.datasets.fracas` — the pure-NLI adapter, with the translation left to the caller

FraCaS is the ninth dataset adapter and the first with NO logic annotation
anywhere: premises, a hypothesis, and a three-valued answer. It earns its
place because that answer maps onto the kit's own verdict without any
interpretive glue — `yes` iff premises ⊨ h, `no` iff premises ⊨ ¬h,
`unknown` otherwise — which makes it a reference target for an NL→logic
pipeline whose TRANSLATION step lives outside this library:
`solve_example(example, translate=…)` takes that step as an injected
callable (a formula string or a kit node per sentence) and the kit only
decides. Nothing in this package calls a model.

The reader was verified against the canonical XML edition and re-measures
what it documents: 346 problems, 536 premises (contiguous 1-based `idx`,
read in index order, not document order), answers `yes` 203 / `unknown` 98
/ `no` 33 / `undef` 12, 41 problems flagged `fracas_nonstandard`. Sections
are not attributes but document-order comment markers, so headings are
tracked while walking and every finer level is reset when a coarser one
changes — a problem can never inherit a stale subsection. Four problems
(276, 305, 309, 310) have an empty question AND hypothesis: they load with
`nl_conclusion=None` rather than being dropped, and `solve_example` refuses
them by name instead of scoring against an absent hypothesis. `undef` is
likewise never filtered away on the loader's own initiative (`answers=` is
how a caller drops it), and since there is no gold FOL, `audit_examples`
reports these examples as ok VACUOUSLY — pinned in the tests so the vacuity
stays a documented property.

The source file carries no explicit licence statement, so it is not
committed here: the tests run against a SYNTHETIC fixture in the same XML
shape (heading resets, reversed `idx`, line-wrapped text, entities, a
question-less problem), and an opt-in test re-measures the real distribution
from `$UFK_FRACAS_XML`. `ace_census` completes the picture in the other
direction: per SENTENCE, what APE accepts as controlled English, with its
own diagnosis attached and no aggregate invented for you.

## [0.25.0] - 2026-08-19

### `drt.reverse` / `ace.formula_to_ace` — "is this formula ACE?" gets an answer

`fol_to_drs` runs the standard translation backwards: it recognizes the
exact SHAPE `drs_to_fol` emits — outer ∃-chains for boxes,
`∀-chain(antecedent → ∃-chain consequent)` for duplexes, `¬∃-chain` for
negations, counting quantifiers over `Part_of` for `Card` — and rebuilds
the box structure. The pinned inverse property is a fixed point:
`drs_to_fol(fol_to_drs(drs_to_fol(d))) == drs_to_fol(d)` NODE-identically
over every mappable corpus DRS and the hand-built shapes. Everything
outside the image refuses by name (`FolToDrsError`): modal operators,
biconditionals, bare universals (no box exports to `∀` without `→`),
counting quantifiers with a non-`Part_of` matrix (the formula-level
counting reading is strictly stronger than a `Card` condition), function
and number terms in argument positions, free variables. Two documented
canonicalizations, both semantically invisible: `Part_of` atoms return as
the typed `Part` condition, and a strict `Card` bound returns shifted
(`Card(g, >, 2)` → `Card(g, >=, 3)` — the same claim over natural
counts).

On top sits the one-liner the feature exists for:
`ace.formula_to_ace(formula)` = `drs_to_ace(fol_to_drs(formula))` —
"expressible as ACE?" becomes two refusal-checked steps whose exceptions
ARE the verdict (`FolToDrsError`: not even a DRS; `AceVerbalizationError`:
a DRS, but outside the probed ACE fragment), and whose positive answer is
a sentence: the donkey formula comes back as "If a farmer X1 owns a
donkey X2 then X1 beats X2.", live-checked through APE and Z3 like every
other verbalization.

## [0.24.0] - 2026-08-19

### `ace` — Attempto Controlled English, via the external APE parser

A new subpackage: ACE text in, kit formulas out. ACE is a controlled natural
language with exactly one reading per sentence, fixed by documented
convention — the reference parser APE resolves the donkey sentence, scope and
cross-sentence anaphora before the kit ever sees a formula. APE is DRIVEN as
an LGPL subprocess (pinned commit `5f4d535`, 2024-04-21), never vendored and
never reimplemented, for the same reason the kit drives Isabelle, E and HETS:
a partial APE clone would be an ACE-shaped language with undocumented
differences, the worst possible property for a language whose entire point is
fixed interpretation rules. Discovery mirrors the E-prover contract:
`$UFK_APE_CMD` (a `wsl:` prefix forces the WSL route) → PATH → a WSL
`ape.exe` → the documented build location `~/APE/ape.exe`, natively and in
WSL, so `git clone … ~/APE && make install` works with zero configuration.

`ace_to_fol(text)` returns one formula per `fof` clause of APE's own TPTP
output through the kit's existing TPTP reader — the donkey sentence lands as
`∀a ∀b ∀c (Farmer(a) ∧ (Donkey(b) ∧ Predicate2(c, own, a, b)) → ∃d
Predicate2(d, beat, a, b))`, events explicit, `ulex=` supplying words APE's
deliberately small built-in lexicon lacks. `ace_coverage(sentences)` reports
each sentence's fate; `run_ape` exposes the raw DRS/TPTP/messages.

The route refuses rather than mistranslates, and each refusal is measured,
not assumed (a hand-written 55-sentence corpus and APE's recorded raw output
for every one of them are committed as fixtures):

- modality, negation as failure, wh-questions and commands are refused by
  **Attempto's own** TPTP translator; they raise `AceTptpUnsupportedError`
  carrying the DRS, which is exactly what the ACE-3 milestone will route
  into the kit's modal family instead.
- a yes/no question SURVIVES Attempto's export — as a TPTP **conjecture**;
  dropping that role would have silently turned "Does John wait?" into the
  assertion that he waits, so a non-axiom role raises too.
- "1 + 2 = 3." comes out as `fof(f1, axiom, (1+2=3)).` — infix arithmetic
  that is neither standard FOF nor in the kit reader's fragment: dedicated
  `AceTptpUnreadError`, raw TPTP preserved (arithmetic reaches the kit via
  the formula route — the ACE-4 section below).
- a non-trivial cardinality survives only REIFIED *on this route* — "At
  least 3 men wait." becomes one witness plus an inert `Object(…, geq, 3)`
  atom with no counting force. `ace_coverage` flags such rows
  (`reified_cardinality`); the DRS and formula routes below carry the
  counting force instead.
- one genuine APE bug, repaired with a proof of narrowness: in a COLLECTIVE
  reading ("John and Mary lift a table.") APE prints the juxtaposed atom
  `(table C)` — not TPTP. There is no legal TPTP in which a lower-word is
  followed by a bare variable inside parentheses, so the repair regex can
  only ever match the malformation; a test runs it over every other
  recorded output (47 rows) and requires zero firings, and a second test
  requires the RAW text to keep failing the reader, so an upstream fix
  retires the repair loudly.

CI builds APE on the Linux legs (seconds — a Prolog qsave, not a C compile;
deliberately uncached, because the saved state is bound to the exact
SWI-Prolog that built it). Without a binary the live tests skip and the
recorded fixtures still pin the whole routing offline.

### `ace.drs_reader` / `ace.mapping` — the DRS itself becomes first-class

APE's native representation is a DRS, and the kit has a DRS core; from this
release the two are connected. `parse_ape_drs` reads APE's printed term into
a 1:1 object model — no renaming, no dropping, no semantic choices — pinned
by a byte-identical round-trip over all 50 non-trivial corpus DRSs, plus a
guard that the corpus actually exercises every condition shape (an atomic
condition with its sentence/token index, `-`/`~`/`=>`/`v` boxes, the four
modal boxes, `question`/`command`, and the list condition `exactly`/`at
most` compile to).

`ace_to_drs` then maps the pure fragment onto `drt`'s classical core, one
vocabulary for everything: nouns/verbs/adjectives/adverbs/prepositions
become kit predicates (events stay, neo-Davidsonian: `See(e1, x1, x2)`), a
non-`pos` degree folds into the predicate name (`Tall_comp_than(x1, mary)`
— no morphology is attempted), the copula becomes EQUALITY with the
be-event dropped exactly as Attempto's own reference translation does it
(guarded: a be-event something else talks about would be kept), proper
names become constants (`john`; a name that would collide with the referent
namespace takes the `c_` form), values become `c_` constants (`c_30`,
`c_Johnny`). Referents are renamed by ROLE — events `e1…`, groups `g1…`,
individuals `x1…` — via a pre-pass, so a name never depends on visit order.

A sentence maps completely or not at all. `map_ace_drs` returns the
per-condition report either way (`DrsMapping.rows`: verdict, reason,
milestone, source position), and `condition_statistics` aggregates it over
a corpus. That aggregate WAS the measured data basis for the ACE-5 core
extension in this same release: it said Card/Part would redeem the group
and cardinality conditions and that "each of" needs no operator of its own
— which is exactly the shape `drt` grew (see below). What still refuses
names its carrier — the `exactly`/`at most` list condition and arithmetic
→ `ace_to_formula` — and commands and negation as failure refuse with no
milestone at all, which is the honest "undecided".

The correctness argument is a differential, not a review: for every corpus
sentence BOTH routes cover (33 — see the ACE-4/5 section below for the
five counted sentences excluded by name), `drs_to_fol` over the mapped DRS is
Z3-equivalent to APE's own TPTP read by the kit's reader — two independent
implementations of the standard translation, one in Zurich and one here,
agreeing formula by formula. The vocabulary alignment that makes the
comparison possible (`ace._align`, private) reuses the mapping's own name
rules, so a wrong alignment rule makes sentences INequivalent and the test
loud, never quietly green.

### `ace.translate` — modality and questions reach the kit's logics

`ace_to_formula` translates APE's DRS straight to ONE kit formula and
carries exactly what the classical DRS core refuses. ACE's four modal boxes
land on the kit's modal family — `must` → `□`, `can` → `◇` (alethic,
Attempto's necessity/possibility gloss), `should` → `Ⓞ`, `may` → `Ⓟ`
(deontic, Attempto's recommendation/admissibility gloss; the split is a
documented choice, and relabeling is one rewrite away). Scope comes out
right because APE's DRS fixes it: "Every man must wait." is
`∀x1 (Man(x1) → □∃e1 Wait(e1, x1))`, universal outside, box inside. Every
modal formula re-parses IDENTICALLY through the kit's own modal parser —
the loop ACE text → APE → kit node → unicode syntax → parser → same node is
closed and pinned — and a live test discharges `□φ → ◇φ` on a serial frame
via `qml_is_valid` to show the nodes are first-class modal citizens.

Questions keep their interrogative force instead of being flattened or
refused: a wh-question yields an OPEN formula (`kind="wh_question"`,
queried variables free and named with their question word — answering is
model finding), a yes/no question a closed one (`kind="yesno_question"` —
answering is entailment). A question mixed with assertions in one text
refuses with "split the text": the merged box shares referents across the
parts, and any split would either break a binding or quantify the premises
into the question.

The translator is the standard Kamp/Reyle translation re-instantiated over
the 1:1 model (the duplex rule included), sharing the mapping's
atomic-condition table — and a three-way differential welds it to the DRS
route on all doubly-covered sentences (38 since the plural milestones
below), which the mapping tests weld to Attempto's TPTP: three
implementations, pairwise Z3-equivalent.

### `drt` — the plural-DRT pair: `Card` and `Part` (ACE-5)

The classical DRS core grows exactly two conditions, both first-class
through the whole stack (constructor validation, box notation, `parse_drs`,
`validate`, `to_dict`, export): `Card(ref, op, n)` bounds a group's
cardinality (`=`, `>=`, `<=`, `>`, `<`; `Card(g, <, 0)` is refused at
construction as unsatisfiable by spelling) and `Part(member, group)` states
membership. `Part` renders and parses as the *binary* `Part_of` — a unary
noun predicate `Part` ("a part") stays legal, and `parse_drs`
disambiguates `Card` by the operator position, so a predicate merely named
`Card` also survives. On export `Card` lowers to the kit's counting
quantifier over a capture-checked fresh membership variable —
`[g | Card(g, >=, 3)]` → `∃g ∃≥3 p1 Part_of(p1, g)` — with the strict ops
shifted exactly (`> 2` IS `>= 3` over natural counts, `< 3` IS `<= 2`;
pinned by Z3 in both directions: `>= 3` proves `>= 2` and refutes its
converse). Deliberately NO `Dist` operator and NO maximality condition:
"each of" arrives from APE as an ordinary duplex over the members (the
data decided — nothing to add), and the `exactly`/`at most` maximality is
a formula-level construct carried by the formula route below.

### `ace` — plurals, cardinalities and arithmetic get their force (ACE-4/5)

The counting gap named in every earlier refusal closes, keeping ACE's own
collective reading of the unmarked plural: "At least 3 men wait." maps to
`[g1, e1 | Card(g1, >=, 3), [x1 | Part_of(x1, g1)] -> [ | Man(x1)],
Wait(e1, g1)]` — one waiting GROUP of at least three men, every member a
man, not three individual waits. Coordinations become closed groups
("John and Mary" → two `Part_of` atoms plus `Card(g1, =, 2)`), "each of"
distributes through the duplex APE already emits (Z3 draws the
consequence: John himself waits), and `has_part`/counted `object` shapes
leave the refusal list — 38 of 50 ACE corpus sentences now map completely
(was 33). The differential against Attempto's own TPTP EXCLUDES the five
counted sentences by name, honestly: APE's reference export keeps
cardinality reified (one witness plus an inert `object/6` annotation), so
demanding equivalence there would demand our translation lose the counting
force too; the exclusion list is welded to the fixture's
`reified_cardinality` flag (mass-noun stays in — its reified object
carries op `na`, nothing was lost).

Two constructs land on the formula route only. The `[...]` list condition
(`exactly`/`at most`) becomes a counting quantifier over the whole scope:
"Exactly 2 dogs bark." → `∃=2 g1 ∃e1 (Dog(g1) ∧ Bark(e1, g1))` — the
DISTRIBUTIVE counting reading (exactly two individual barkers), a
documented semantic choice at `translate.box_with_lists`: collective
maximality ("no third group") is not first-order expressible, and the
mixed-list guards refuse anything whose reading would be ambiguous. And
APE's `formula`/`expr` conditions translate to kit arithmetic —
`"1 + 2 = 3."` → `1 + 2 = 3` with `+`/`-`/`*`/`/` as kit `Function` terms
— where the default backend deliberately keeps `+` uninterpreted
(measured) and `atp.z3_arith.is_valid_arith` decides the fragment (proves
`1 + 2 = 3`, refutes `1 + 2 = 4`). The corpus grows its 55th sentence
("More than 2 men wait.") to pin the strict-`greater` op live, and the
fixture is re-recorded: 38 ok / 11 tptp_unsupported / 5 not_ace /
1 tptp_unread.

### `ace.verbalize` / `ace.chem_lexicon` — the pipeline runs backwards (ACE-6)

`drs_to_ace` verbalizes a kit DRS as ACE text plus the APE user-lexicon
entries that carry its content words, and `ace_round_trip` is the machine
self-check: text back through APE and the mapping, judged by Z3 against
the input. Every mappable corpus sentence closes that loop (38/38, pinned
live in `tests/test_ace_verbalize.py`) — including the counting shapes
("There are at least 3 mans X1. X1 wait."), coordinations ("John and Mary
lift a table X1."), "each of", genitives, comparatives and value copulas.
The claim is deliberately NOT natural English but MEANING, machine-checked:
surface forms are mechanical and lexicon-defined (3sg/plural add
`s`/`es`/`ies`, comparatives `er`/`r`/`ier`, underscores become hyphens —
`Bond_to` is the verb `bond-to`; "3 mans" is intentional, its
`noun_pl(mans, man, neutr)` entry defines the surface and the logical
symbol underneath is exactly `man`). Every generation decision was probed
against the live APE before being written, and two probes shaped the
design: "It is false that A and B." DROPS `B` out of the negation scope —
so a multi-clause negated box is rewritten as `∀(front → ¬back)` (a
classical equivalence, re-checked per DRS by the round trip) — and "less
than"/"at most" come back as the maximality list, so upper-bound `Card`
conditions refuse rather than round-trip wrongly. Everything else outside
the probed fragment refuses by name (`AceVerbalizationError`): values
outside equalities, binary predicates over individuals (an ACE verb always
carries an event), non-invertible names (the surface must map back to the
SAME kit symbol through the mapping's own name rules — checked per name),
groups beyond the three probed shapes, deep nesting.

`chem_ulex` renders the ChemLog signature as such a user lexicon — ACE
about molecules: "There is a carbon X1. X1 bonds an oxygen X2. X1 is
aromatic." parses with the DRS carrying `c`, `bond`, `aromatic`. Elements
and `atom` are nouns, atom properties adjectives, binary relations
transitive verbs; a coverage test pins that the three tables plus the
documented nullary exclusion (`net_charge_neutral` and friends — a
sentence needs a subject) tile the signature EXACTLY, so signature drift
lands loudly. Two shape facts are documented rather than hidden: kit-side
the symbols arrive capitalized (`ace_kit_name` computes the spelling), and
ACE verbs are neo-Davidsonian, so binary ChemLog relations arrive with an
event argument (`Bond(e1, x1, x2)`) — projecting the event away is the
caller's explicit step, never a silent one.

### `drt` — the name conventions catch up with the 0.23.1 grammar

Found by the ACE mapping, fixed at the root: 0.23.1 widened the GRAMMAR's
PREDICATE and NAME to accept underscores in continuation (that is how the
chem vocabulary's `Has_bond_to` is writable), but `drt.nodes` still
enforced the pre-0.23.1 rules — so a predicate or constant the fol parser
happily produces (`Has_bond_to`, `john_smith`) could not be put in a DRS,
and `parse_drs`'s tokenizer split `Has_bond_to` at the first underscore.
`is_predicate_name`, `is_constant_name` and the box-notation tokenizer now
follow the live grammar (verified against the parser: `a_b`, `ab_`,
`john_smith` are constants; `a_1` and `x_` are not, keeping the referent
namespace clean). Same lesson as 0.23.1 itself: an evidence corpus only
covers the positions that occur in it — the widening landed in the grammar
and the chem tests, and the DRS position went unchecked until a comparative
adjective needed `Tall_comp_than` in a box.

## [0.23.2] - 2026-08-19

A patch number for a release that changes how formulas are parsed. That is
deliberate and it is worth saying out loud rather than burying: semantically
this is a minor release. It ships under 0.23.2 by the maintainer's decision,
so read the two sections below before upgrading if you depend on exact error
strings or on `ⓄP` meaning something other than `Obligatory(P)`.

### Tests — a Z3 timeout can no longer read as a disagreement

`tests/test_lj_search.py` cross-checks its curated intuitionistic battery against
three independent procedures, the third being the GMT→S4 translation decided by
Z3. That third check went through `atp.z3_models.is_valid`, which folds Z3's
`unknown` into `False`. Right for a validity oracle — a non-proof is not a proof —
and wrong here, because it turns "Z3 ran out of budget" into "the procedures
disagree", which is the one thing this battery exists to detect. Under eight-way
xdist contention the battery therefore failed intermittently on a formula that
answers in 8 ms when asked on its own.

The budget is no longer what decides it. `_gmt_verdict` mirrors `is_valid`
exactly — same negated query, same solver options, same random seed — and keeps
the third answer: `True` (proved), `False` (counter-model), `None` (gave up).
A timeout now reports as unavailable, a counter-model still fails immediately,
and the retry budget went 20 s → 60 s only to make "unavailable" rarer. The short
`_GMT_TIMEOUT_INVALID` (2 s) is unchanged: on the invalid side `unknown` and
`refuted` lead to the same expected verdict, so collapsing them costs nothing,
and raising it would take the random differential from 30 s to about 285 s.

Two tests guard the new helper, and neither of them consults a clock. One
intercepts the query `gmt_is_s4_valid` hands to Z3 and requires the mirror to
build that same query, for all 25+ curated formulas, so a parameter added to the
public route cannot silently leave this battery cross-checking a different
question. The other patches `check` to answer `unknown` and requires `None`
rather than `False`.

Both started out timing-based, and the first shape of the first one was flaky in
exactly the way this section is about: it ran the two routes at the 2 s budget
and demanded the same verdict, so the one-off context rebuild could land on one
run and not the other. It did — `Glivenko ¬¬Peirce` came back True from the
mirror and False from the public call on four of five CI legs, minutes after the
tag. Corrected on main right after; the package code is untouched, so 0.23.2 on
PyPI is unaffected and there is no 0.23.3 for it.

### Docs — the build is warning-free again

Sphinx had been reporting one warning for a while: `duplicate object description
of unicode_fol_kit.fol.spans.SpanMap`. `SpanMap` is defined in `fol.spans`,
re-exported by `chem` (whose `rename_with_spans` / `to_chemlog_names_with_spans`
carry a caller-supplied one across the rename), and named in `chem.__all__` —
which is enough for `automodule` to describe it a second time, on the chem page.
Both descriptions register the same canonical name, hence the warning, and the
`[source]` link on the chem copy pointed at `fol/spans.py` anyway.

The class keeps its own page and `chem.__all__` is untouched, so
`from unicode_fol_kit.chem import SpanMap` and `import *` are unaffected; only
the second description is gone.

### `fol._identifiers` — an operator glyph is no longer an identifier character

`Ⓞ` is the deontic Obligatory operator. Unicode also says `"Ⓞ".isupper()` is
True, and since 0.23.0 that test is exactly how the kit decides "this character
opens a PREDICATE". So `ⓄP` had two readings at once — `Obligatory(P)`, and the
atom whose predicate is named `ⓄP` — and nothing chose between them on purpose.
Asked for every derivation (`ambiguity="explicit"`), lark reported the node as
ambiguous; asked for one, its Earley parser returned the operator reading while
a table-driven lexer returns the other. Seven glyphs were in that state:
`Ⓒ Ⓕ Ⓖ Ⓝ Ⓞ Ⓟ Ⓤ`.

They are now carved out of every letter class, on the same rule and for the
same reason as `λ` and `μ`: a glyph that is a registered operator ANYWHERE is
not an identifier character ANYWHERE. The carve-out is a list of symbols the
grammar already spends, not a swipe at a Unicode block — `Ⓐ`, the other circled
capitals and the Roman numerals stay writable, and `tests/test_operator_glyphs.py`
checks both halves against the LIVE registry, so a newly registered letter-like
operator fails there instead of quietly becoming a name.

What changes for you: `AⒸB` used to be one predicate named `AⒸB`; it is now
`A Ⓒ B`, a Contrast. Every one of the 61 uses of these glyphs across the kit's
own tests and docs was already an operator use, so nothing in the suite moved.

The same applies inside a name, not just at its start: `FooⒸBar` was one
predicate and is now a Contrast between two. An AST built directly with that
name therefore no longer survives `to_unicode_str()` -> `parse()`. That is not
new behaviour so much as seven more characters joining a set that already had
members: the AST layer performs no name validation at all, so `Atom("Foo→Bar")`
has always come back as `Implies(Foo, Bar)`, and `Atom("Foo Bar")` has always
come back as a NamingError. If you construct atoms from unchecked strings, run
them through `fol/sanitize.py` as before.

Only SINGLE-character symbols are carved out. `K_`, `B_`, `Say_`, `Want_` open
with ordinary capitals that obviously cannot be excluded, and do not need to
be: their terminals cover the whole `K_alice`, so longest-match settles it with
no ambiguous node.

### `fol.msflparser` — LALR for the eight non-modal modes

Earley is the right default for a grammar that needs it. This one does not:
asked for every derivation, the classical grammar produces exactly one for all
1260 parsable lines of the 1310-line FOLIO fixture. It was paying for a capability it never used.

The eight non-modal modes are now parsed with `parser="lalr"`. Measured on the
kit's own corpus, **30x to 50x** faster inside lark across the six modes that accept a corpus
worth timing (`msfol` and `msfl` accept 6 FOLIO lines between them, FOLIO
being unsorted, which is too few to time), and **200 -> 6513 formulas/second**
end to end through `MSFLParser.parse`, 4.99 ms -> 0.154 ms per formula, a
32.5x speedup. Median of seven runs with the garbage collector disabled, the
"before" side being a real `MSFLParser` switched back to Earley rather than a
reconstruction of the old path. Identical trees, identical accept/reject sets, and identical source
spans — the last checked separately, because lark's `Tree.__eq__` ignores
`meta` and `parse_with_spans()` reads exactly that: 4815 formula-level span comparisons
across the eight modes, zero differences.

`modal` keeps Earley, for a reason rather than out of caution. After the glyph
carve-out above the two agree on every tree, but eight inputs in the kit's own
corpus are still accepted by Earley and refused by the LALR table, all of one
shape: a bare lowercase propositional atom or a nominal standing as a whole
formula — `p→(q→p)`, `¬(p∧q)→(¬p∨¬q)`, `@i (P ∧ ◇j)`. Those are legal modal
syntax, so moving that mode would be a silent narrowing of the language, not a
speedup.

The error model survives intact, and the mapping that keeps it was measured
rather than guessed. Earley's dynamic lexer only offers tokens the parser can
currently use, so a well-formed symbol in the wrong place never became a token
— it stayed an unscannable character, and the kit raised `NamingError`. LALR
tokenises first and refuses afterwards, so the same input arrives as
`UnexpectedToken`. Over the 1310-line FOLIO fixture the two line up exactly, with no
overlap in either direction:

    Earley UnexpectedCharacters  ->  LALR UnexpectedToken, token != $END
    Earley UnexpectedEOF         ->  LALR UnexpectedToken, token == $END

So `$END` routes to `ParsingError` and everything else to `NamingError`,
reported against the offending token's first character — the character Earley
used to name, carried on a real `lark.UnexpectedCharacters` so the
`UnexpectedInput` API `NamingError` inherits (`match_examples()` above all)
keeps working. Over the 1310-line FOLIO fixture plus eight hand-written
malformed shapes, 58 inputs are rejected in `fol` mode: **0 error-class
changes**, 26 messages byte-identical, and 32 that differ, all of them `Incomplete formula … Expected: …`,
where LALR knows precisely which tokens could continue and Earley over-listed;
`tests/fixtures/folio_fol_strings_nonparsable.txt` carries 31 of them as a
reviewed diff, with the same 50 lines rejected before and after. As a
side-effect the narrower list stops leaking lark's internal `__ANON_5` terminal
name into user-facing text.


### `fol.naming` — a failed parse no longer rebuilds lark's lexer

Reported from a campaign evaluating model-generated formulas next to vLLM: one
failed parse took **185 s**. The same call takes 13 ms on the same kit, the
same lark and the same Python. The only difference is whether the package
`interegular` happens to be importable.

Three things line up to produce that. `NamingError` names the token in FRONT of
the offending character ("Invalid predicate 'Foo' - unexpected character ..."),
so it tokenises the failing text a second time; lark's exception cannot supply
that token, because the Earley scanner leaves `token_history` at None and knows
only the character and the position. That second pass went through
`Lark.lex()`, and formulas are parsed with `parser="earley"`, which lexes
dynamically and keeps no standing lexer -- so `Lark.lex()` constructed a fresh
`BasicLexer` on every call. And `BasicLexer.__init__` runs a terminal-collision
check whenever `interegular` is importable, comparing every pair of
same-priority terminal regexes. Since 0.23.0 the identifier terminals are
generated at import from the running interpreter's Unicode tables, and
comparing THOSE takes minutes -- not because the patterns are long (measured
across all nine grammars, the largest is NAME at 4856 characters and the rest
are 1.0 to 1.8 kB) but because interegular decides collisions by intersecting
one finite automaton per pattern, and these range over most of the Unicode
letter repertoire.

Nobody asks for it. `interegular` arrives as a transitive dependency of vLLM
via `outlines`, so every environment that evaluates model output has it without
having requested it -- and failed parses are the normal case for model output,
not the exception. The cost was also invisible: the call looks like an ordinary
parse and takes four orders of magnitude longer, which reads as a hung worker.
The reporting run lost an hour to it and then died with 187 OOM kills.

The lexer used for error messages is now built once per parser and kept, with
lark's validation switched off. Both halves earn their place: caching pays the
check once per parser instead of once per failed formula, and skipping it
removes the check altogether. Nothing is lost by skipping -- validation checks
that the GRAMMAR is well formed (terminal regexes compile, no zero-width
terminal, every `%ignore` name defined), which lark established when it built
the parser, and it only ever raises or stays silent; it never influences which
tokens come out. Verified rather than argued, on both routes and against every
one of the nine distinct grammars the kit builds: token type, text and offsets
identical on valid formulas, malformed ones and every proper prefix of both --
2952 comparisons in the development differential, and 1971 in the regression
test that ships with it (`test_tokens_match_larks_own_lexer`, whose corpus is
the smaller of the two).

Measured on the reporter's formula, with `interegular` present: 185.192 s for
one failed parse before, and after -- across three repeats on an idle machine
-- 0.013 to 0.028 s for the first failure, then 3.9 to 4.6 ms for each one
after it. Without `interegular` the same path also improves, 13 ms -> about
4 ms, because the scanner is no longer recompiled per failure.

Building that lexer is allowed to fall back to `Lark.lex()` -- lark could
rename its internals, or refuse a grammar only its own validation would have
diagnosed -- but USING it is not, and that distinction is load-bearing. The
first cut of this fix wrapped the whole thing in one `except Exception`, which
also caught the `UnexpectedCharacters` raised by the malformed text itself and
then retried through `Lark.lex()`: full price, for exactly the inputs the
change exists to make cheap, ending in the same exception. Measured at one
fallback per unlexable input before the split and none after.

The reporter's own first suggestion -- drop the second tokenisation and read
everything out of lark's exception -- was not taken, and deliberately so: with
`token_history` at None it would cost every "Invalid predicate 'Foo'" message
its name, leaving only the character and the offset. Naming the refused token
is the reason `NamingError` exists; a model reading the error in order to retry
needs to know which name was refused.

`tests/test_error_path_speed.py` holds the line with a call count rather than a
wall-clock number -- "the collision check never runs on the error path" is
exactly what was wrong and is stable across machines. Its first test proves the
probe fires by showing that lark's own route still trips it, so the rest cannot
pass vacuously on a kit where the fix was reverted.

Checked and NOT affected: the kit's five other lark parsers. The two LALR ones
(`eval/datasets/proverqa`, `eval/datasets/willow`) pay the check once at import
on small ASCII grammars, 0.089 s in total; the three Earley ones
(`fol/prover9_input`, `fol/tptp_input` x2) build no `BasicLexer` at all and
never call `lex()`.

## [0.23.1] - 2026-08-18

### `fol._identifiers` — the underscore reaches predicate position too

0.23.0 widened the identifier terminals but did it asymmetrically: `_` became
legal in the term-valued terminals (NAME, CONSTANT) and stayed illegal in
PREDICATE and SORT. The stated reason was that keeping it out of predicate
position left an IRI-shaped name such as `Http___www_w3_org_owl_Thing` as
illegal a token as it had always been, which `fol/sanitize.py` was said to rely
on. It does not: `sanitize.py` carries its own deliberately ASCII-strict
`_PRED_RE` and reaches its verdict without consulting the grammar, so it
rewrites that IRI either way — as its updated test now states outright.

What the asymmetry did break is the chemical vocabulary. `chem/interop.py`
spells a ChemLog predicate for the kit by capitalising the FIRST character and
nothing else, so `has_bond_to` becomes `Has_bond_to` — and 17 of the chemical
signature's 40 predicates carry an underscore that way: `In_ring_of_size_6`,
`Net_charge_neutral`, `Carbon_connected`, `Same_fragment` and the rest. Every
one of them was a token the kit's own parser refused, which made the chemical
vocabulary impossible to write down in the kit's own surface syntax at all.
The failure did not surface as a parse error where it belonged. Handed the
signature and told to use it, a generating model wrote `Has_bond_to(c, x)`, was
refused by the parser, and fell back to `HasBondTo` — which parses, but is in
no signature, so the model checker returned an uninterpreted-symbol error for
every molecule rather than a verdict. 400 of 400 in the run that found this.

PREDICATE and SORT now take the same continuation class as NAME. The underscore
remains a continuation character everywhere: `_Family(x)` and `∀x :_History` are
rejected as before, since the first character is what carries the
predicate-versus-term distinction. CONSTANT's `c_` form deliberately keeps the
narrower tail — its leading `c_` is the marker, and letting the tail carry more
underscores would widen the span it competes with NAME over.

The test that was missing is the one that would have caught this: rather than
sampling identifiers by hand, `tests/test_identifier_widening.py` now walks
every entry of `chem.interop.KIT_TO_CHEMLOG` through `parse` and asserts each
one comes back as an atom headed by that exact name, so a predicate added to
the signature later is covered without anyone remembering to add a case. Every
underscore case in 0.23.0's tests came from the FOLIO corpus, where they all
sit in term position — which is exactly why the gap in predicate position went
unnoticed.

## [0.23.0] - 2026-08-18

### `fol.grammars` / `fol._identifiers` — identifiers widen past ASCII, underscores, and digit-leading names

`PREDICATE`, `CONSTANT`, `NAME`, and `VARIABLE` were each one fixed ASCII
regex (`[A-Z][a-zA-Z0-9]*` and siblings), so a name that was not plain
`A-Za-z0-9` never parsed at all. Run against the FOLIO gold corpus
(`tests/fixtures/folio_fol_strings.txt`, 1310 lines), 96 lines failed —
and 46 of them failed at exactly this seam, not at some deeper grammar
limitation: a digit-leading name (`Hosted(beijing, 2008SummerOlympics)`,
17 lines), an underscore inside a name (`dani_Shapiro`, `family_History`,
15 lines), or a non-ASCII letter (`LostTo(x, świątek)`, 14 lines). The
remaining 50 are genuine gold-corpus defects, unrelated to identifiers and
left rejected: 44 lines with unbalanced parentheses, 5 that mix `∧`/`∨`
without brackets (a mix this grammar has always refused outright, on
purpose — two different readings, and picking one would be a guess), and
one formula using the wrong biconditional glyph (`⟷` instead of `↔`).

`PREDICATE`/`CONSTANT`/`NAME`/`VARIABLE`/`SORT` are now generated at
runtime, once per process (`fol._identifiers`, scanning `str.isupper()`/
`str.isalpha()` over the running interpreter's own Unicode tables) rather
than hand-typed as a frozen codepoint range — a range pasted into source
would go stale the moment Unicode gains a script or a codepoint's category
changes, silently drifting from whatever Python 3.10+ actually runs the
kit. The rule that decided PREDICATE vs. term position never changed, it
just widened honestly to alphabets it was never tested against before:
the FIRST character's `str.isupper()` decides — true means PREDICATE,
anything else means term-valued (NAME/CONSTANT/VARIABLE). Most scripts
(CJK, Arabic, Hebrew, Devanagari, …) draw no upper/lower distinction at
all, so `str.isupper()` is always false there and a bare identifier in
such a script is always term-valued, never able to head an atom by
itself — not a special case, just what the existing rule says once it is
applied to a script that has no case to signal with. A digit-leading name
(`2008SummerOlympics`) is folded into `NAME` rather than a new terminal —
digits then a letter then the ordinary continuation — so it is always
term-valued too and can never open an atom; `NUMBER` itself is completely
unchanged (`2008` and `2.5` still lex as `NUMBER`). Continuation
characters (position two onward) additionally gained `_` and Unicode
combining marks (categories Mn/Mc), the latter so an NFD-decomposed name
(`ś` → `s` + U+0301) still lexes as one identifier instead of a letter
plus a stray mark.

Greek and Coptic (U+0370–U+03FF), Greek Extended (U+1F00–U+1FFF), and
U+2126 OHM SIGN are excluded from every generated class: `λ` is the
LAMBDA terminal, `μ` is the measure-term operator, and the plain lowercase
Greek run is already `CONSTANT`'s second alternative — widening the letter
classes without carving Greek back out would have turned those operators
into ordinary identifier characters. Widening `NAME` to accept `_` also
means `CONSTANT`'s `c_...` form and `NAME`'s alpha-leading form can now
match the exact same span (`c_alpha` never overlapped before, because
`NAME` never accepted an underscore) — `CONSTANT`'s existing priority
(`.3` over `NAME`'s `.2`) still wins that tie, now for a real reason
instead of an accident of spelling; the `c_` form itself may also carry
Unicode letters (`c_świątek`). `fol.sanitize` — the layer that rewrites an AST's names to
tokens THIS parser's own grammar can re-parse, for a name from outside the
kit (an imported TPTP IRI dump, typically) that the grammar does not
accept as-is — is deliberately untouched: its job is re-parseability by
this parser, not legality for any particular export format (a separate
concern, closed for TPTP/Prover9/SMT-LIB2/THF/Isabelle/MiniZinc export by
the fix described further down in this entry), and widening its own
ASCII-only patterns to match this now-Unicode-wide grammar would only let
a name back through parsing that is still illegal wherever it must
eventually export to. `fol.dialect_repair`'s legality check
(which functor-position names are worth renaming when a formula fails to
parse) now asks the same generated classes rather than `sanitize`'s
ASCII-only ones, so a name like `family_History` is recognised as already
legal instead of being needlessly rewritten. `fol.naming.NamingError`
shows a short hand-written description of each widened terminal's shape
in its "Expected pattern" text instead of the several-kilobyte generated
regex, which is not something a human — or a model reading the error to
retry — could act on.

The two name shapes this widening lets past the parser — a non-ASCII
letter in predicate/function position, and a digit-leading term — used to
reach every export format unchanged or nearly so: `Atom.to_tptp`/
`to_prover9` and `Function.to_tptp`/`to_prover9` emit the predicate/
function name close to verbatim (TPTP folds only the first character's
case; Prover9 folds nothing), `hol.classical`'s `_sanitize` ran
`str.isalnum()` over a name without transliterating first (`True` for
nearly every Unicode letter, so `świątek` passed straight through),
`atp.minizinc_backend` transliterated a constant's name but not a
predicate's or a function's, and a digit-leading name reached
`to_z3`/`Solver.to_smt2()`'s SMT-LIB2 text with no quoting at all — text
that does not parse back. None of this was new *in kind*: a
`Constant`/`Atom`/`Function` built directly in Python, without going
through this parser at all, could already carry such a name and hit the
same exporters. What the widening added was a second, ordinary way to
arrive at one, so the gap stopped being a corner case reachable only by
hand-built AST and became something a parsed FOLIO-style sentence hits
directly.

Every one of those gaps is closed now, and the fix does not live inside
any node's own `to_tptp`/`to_prover9`/`to_z3`. A single node has no view
of what any other node in the same problem is named, so a per-node rename
cannot keep two distinct kit-level names from colliding on their fix, and
it never reaches a caller that later needs to read a prover's own symbol
names back out. The fix instead sits where a whole problem or theory is
assembled: `atp._tptp_problem.generate_tptp_problem`/
`..._with_mapping` (shared, unchanged, by `atp.vampire_entailment`,
`atp.eprover_backend`'s E and Zipperposition routes, and
`atp.twee_entailment`) and `atp.prover9_entailment
.generate_prover9_input_with_mapping` each walk every premise and the
conclusion TOGETHER, leave a name that is already legal for that target
completely untouched, and replace only the rest with an ASCII,
non-digit-leading token — injective and consistent across the whole
problem, via a shared reservation set that is filled in two passes
(collect every name first, only then synthesise a token for the ones that
need one) so a synthesised token's collision-avoidance never depends on
which order the premises happen to be given in. `hol.classical._sanitize`
(THF/Isabelle, classical and MSFOL) and `fol.qml`/`hol.isabelle_modal`'s
THF/Isabelle modal exporters now transliterate via `constant_name_to_ascii`
*before* their existing alnum-or-underscore filter runs, and the modal
exporters gained a de-colliding resolver for bound variable names, which
they had not had before. `atp.minizinc_backend`'s predicate, function, and
variable names now transliterate the same way its constant names always
did, with predicates and functions also gaining the collision guard only
constants had. `atp.cvc5_backend` needed a narrower fix, because Z3's own
`Solver.to_smt2()` already pipe-quotes a non-ASCII name correctly on its
own (checked live: `świątek` round-trips through it with no help from this
kit) — only a pure-ASCII, digit-leading name still produced unquoted,
unparseable SMT-LIB2 text, and reproduced live, feeding one to this
backend before the fix does not raise a catchable error at all: cvc5's
`InputParser` segfaults the whole Python process.

A prover's own answer carries these sanitised names back — a TSTP proof
step, raw stdout, an SZS status detail, a cvc5 countermodel — so every one
of these routes also translates its answer back to the original kit-level
names before it reaches the caller, via a `TptpNameMap`/`Prover9NameMap`
each `..._with_mapping` function hands back alongside the problem text.
`atp._tptp_problem.apply_reverse_tptp` and `atp.tstp.reverse_map_derivation`
handle a parsed, structured proof step; the new `atp._ascii_names
.reverse_map_text` handles free text. The free-text side exposed a real
bug while it was being built, caught live against a real prover rather
than assumed: keying the reverse dictionary by the raw token chosen before
rendering is correct for the structured route (re-parsing a prover's TSTP
text re-applies the kit's own capitalisation convention on import) but
wrong for text a prover echoes back UNPARSED, because `Node.to_tptp` also
folds the first character of whatever it exports — so a plain, already-
legal predicate like `Human`, never touched by sanitisation at all, still
came back through E's or Vampire's own stdout as `human` and was never
translated back. `TptpNameMap.reverse_rendered()` fixes it by keying the
reverse dictionary on the token actually written into the exported text
instead; checked live against a real E 3.5.1 and a real Vampire 5.0.1
(both via WSL) on a `Human`/`Mortal` and a `Świątek`/`2008SummerOlympics`
battery, with the reverse-mapped derivation step (which was already
correct, being on the structured route) as the control showing the
free-text side was the only one broken. `atp.cvc5_backend` reverse-maps
and un-quotes its countermodel the same way, checked live on the same
battery.

None of this touches `Node.to_tptp`, `Node.to_prover9`, or `Constant.to_z3`
themselves — they still render a name close to verbatim, exactly as
before, and that stays deliberate rather than an oversight: a
`Constant`/`Atom`/`Function` assembled directly in Python, never passed
through one of the problem-generation entry points above, can still carry
any name at all, and the whole-problem view a consistent rewrite needs
only exists once premises and a conclusion are actually gathered into one
problem. `fol.sanitize.sanitize_names` — described above as the layer that
makes an imported name re-parseable by this parser — looks like the
obvious tool to reuse here, and was deliberately not: its target is
re-parseability by the kit's OWN grammar, not any export format's, and the
two disagree often enough to matter — `fol.sanitize` rewrites the
already-TPTP-legal single-letter constant `a` to `c_a`, which would break
the "an already-legal name passes through byte-identical" guarantee every
route above makes. The new `atp._ascii_names` module reuses the same
SHAPE `fol.sanitize.NameMapping` already established — a shared
reservation set, numeric-suffix de-collision, a flat reverse dict — built
fresh per target format instead of reusing its kit-specific methods.

One path stayed unverified against a real prover, named here rather than
left implicit: Prover9 has no route anywhere in this kit that reads a
proof or a countermodel back out of Prover9's own output —
`check_logical_entailment` reports a bare proved/not-proved verdict — so
there was no reverse mapping to build there in the first place, and no `prover9`
binary was reachable from this machine (checked `PATH` and WSL) to test
the export direction against the real thing either; the kit's own
`prover9_input.parse_prover9` reader served as the touchstone instead.
Everything else above was checked against the real tool it targets: E
3.5.1 and Vampire 5.0.1 (via WSL) for TPTP, Twee 2.6.1 (via WSL) for the
equational fragment — proving and correctly reverse-mapping a
`świątek`/`2008wins` equation live — and an installed `cvc5` for
SMT-LIB2, including reproducing the digit-leading segfault above live,
before confirming the fix round-trips through `z3.parse_smt2_string`.

Every string the parser accepted before this change still parses to the
structurally identical AST: verified by diffing this parser against the
one committed at HEAD before the change, over all 1310 FOLIO lines — the
1214 that already parsed produced byte-identical ASTs, and exactly the 46
described above newly parse.

### `fol.msflparser` / `fol.spans` — a parsed formula can point back at its own text

A formula that parsed cleanly never carried any link to the text it came
from: `MSFLParser` built its Lark grammar without `propagate_positions`, so
the parse tree carried no offsets, and positions existed only on FAILURE —
`NamingError`/`ParsingError` build them from Lark's own exception. Nothing
downstream (repair, simplify, the chemical tools' "which conjunct is too
permissive" feedback) could say WHERE in the source text a subformula sits.

`MSFLParser.parse_with_spans` closes that gap, alongside `.parse` rather
than replacing it: it returns a `SpannedFormula` — `.formula` is exactly
what `.parse(text)` would build, `.spans` a `SpanMap` from each of its
nodes back to the slice(s) of `text` it was parsed from. Every node gets
TWO spans (`NodeSpans(extent, head)`): `extent` is the minimal text the
node covers (redundant outer parentheses excluded), `head` is just its own
head token — a connective's occurrence, an atom's predicate name, a
quantifier's symbol together with its bound variable including the
whitespace between them (`"∀ x"`); a leaf term has `head == extent`.

The spans live in a side table beside the AST, not as a field on `Node`:
every node is a frozen dataclass with structural equality and hashing —
dedup, `canonical_key` caches, sets of nodes, the harvest cache in
`semantics/model_eval.py`, and every test that compares a parsed formula to
a hand-built one all depend on that holding. A span *field* would make two
structurally identical formulas parsed from different source text compare
unequal and hash apart, so the table stays external, and `parse_with_spans`
changes nothing about how `.formula` itself is built.

Within that table, the key is PATH — a tuple of child indices from the
root, the SAME convention `fol.spans.traverse`/`fol.nodes.node_at`/
`fol.nodes.replace_at` all agree on — never node identity or node value:
a value-keyed table would collapse two textually-distinct occurrences of
the same subformula (`P(x)` in `P(x) ∧ P(x)`) onto one span, and an
id()-keyed one goes stale the moment a node is rebuilt, which the
scope-resolution rewrite that runs after parsing (and, in modal mode,
agent-variable resolution) always does — `map_children` reconstructs every
node it touches, even a lambda-free formula with nothing to actually
rewrite. A path denotes the same structural position regardless, so it
survives that rebuild for free;
`fol.spans.project_spans` carries the table across a rewrite that is NOT
shape-preserving (the one case: a higher-order lambda application, rebuilt
into fresh `Application`/`LambdaVar` nodes the original parse never
produced). `SpanMap.for_node(node)` is the convenience form for a caller
holding a node object rather than a path, resolved by identity against
whichever tree the map is currently bound to.

A span that cannot be recovered reports `UNKNOWN`, never a guessed or
interpolated one. For the classical FOL fragment (`∀ ∃ ¬ ∧ ∨ → ↔ ⊕` and
predicates over constants/variables/function terms) both spans are exact
for every node — checked over the 1310-formula FOLIO gold corpus
(`tests/fixtures/folio_fol_strings.txt`, MIT), with the handful of
non-parsable gold lines committed as
`tests/fixtures/folio_fol_strings_nonparsable.txt`. Outside that fragment
(modal/lambda/second-order/counting operators), `head` may legitimately be
`UNKNOWN` — two narrow, already-known cases: a higher-order lambda
application built by a rewrite the original parse never produced, and an
agent variable sliced out of a combined `K_a`-style token (the enclosing
`Knows`/`Believes`/… node's own `extent` is unaffected either way).

`chem.interop` gets the matching propagation step, `rename_with_spans` /
`to_chemlog_names_with_spans`, since the kit-to-ChemLog vocabulary rename
every chem tool runs first also reconstructs every node in the tree — a
shape-preserving rewrite, so every path in the table still means the same
thing after it, no projection needed.
`mcp.chem_tools.check_molecule` / `check_molecules` / `explain_molecule_failure`
take a new `with_spans=True` (default off, byte-identical output otherwise)
that adds a `"span"` key beside `failing_conjunct` — a caller gets a
character range straight into the formula it submitted, instead of having
to find the rendered `failing_conjunct` text again inside the original
string by eye.

### `chem` — the halogens enter the vocabulary

`mol_to_structure` types `F`, `Cl`, `Br`, `I` and `At` as `f`/`cl`/`br`/`i`/
`at`, and `CHEMLOG_SIGNATURE` declares them (40 predicates, up from 35).

ChemLog's published vocabulary is a peptide one, so it covers C/N/O/S/P/H
and stops there — and a molecule containing any other element was refused
outright. Measured against the ChEBI corpus that is not a small edge: **5049
of the 35 459 molecules** in the reference run could not be built at all, and
whole classes (`organohalogenCompound` and its kin) are *defined* by the very
atom that made them unbuildable. A refusal is not a chemical statement: those
classes came out unanswerable rather than answered.

Anything outside the eleven letters — a metal, say — is still refused with a
`ValueError` naming the element, because silently dropping an atom's type
predicate would misrepresent the molecule. Astatine is included for closure
of the group despite being vanishingly rare in ChEBI; leaving one member out
would make the vocabulary's boundary an accident of frequency.

### `fol.nodes` — `replace_at` / `node_at`, a public path-addressed tree editor

A consumer that wants to mutate one subformula of a parsed AST — swap a
connective, negate an atom, substitute an argument term — previously had to
either hand-roll a `map_children`-based rewrite for each node type it might
hit, or use `atp.resolution`'s private `_replace_at`, which only ever
addresses an `Atom`/`Function`'s argument positions. `replace_at(root, path,
new_node)` (and the companion read-only `node_at(root, path)`) are the
general, public counterparts: they work over any node — formula or term —
so a path is a tuple of child indices, `()` addressing the root itself.

The path convention is `Node._child_nodes()`'s existing, already-relied-on
child order (the same order `map_children`/`walk`/`count`/`depth` use) for
every node EXCEPT `Quantifier`, whose bound variable is deliberately
excluded: a `Quantifier`'s only path child is its `formula`, at index 0 —
the SAME convention `fol.spans.traverse`/`fol.spans.SpanMap` use, so a path
one hands out is valid input to the other. (The variable is folded into the
quantifier's HEAD span instead, the same way `Node._tree_parts()`/`to_dot`
already fold it into the node's *label* rather than its *children* — see
`fol.spans`'s module docstring for the full reasoning.)

The guarantee that makes it safe to build a larger edit on top of: any path
that does not run through the replaced subtree addresses the exact same
object — not just an equal one — in the result, because every node off the
root-to-target spine is carried over by reference rather than copied; only
the spine itself is rebuilt. See `tests/test_replace_at.py` and
`tests/test_spans.py`'s edit-stability test.

### `fol.nodes` — two API commitments made explicit

Two things a caller assembling and re-serialising ASTs across a process
boundary already depended on are now documented as STABLE PUBLIC API rather
than left implicit: every node class's constructor (field names, order, and
meaning) and `Node.to_unicode_str()`, including its roundtrip guarantee —
`parse(n.to_unicode_str())` is structurally equal to `n` for the classical
FOL fragment (`∀ ∃ ¬ ∧ ∨ → ↔ ⊕` and predicates over constants/variables).
That guarantee is now exercised by a dedicated property suite,
`tests/test_fol_fragment_roundtrip_b2.py` (hand-built parenthesisation edge
cases plus a seeded randomized search), alongside the existing
example-based `tests/test_to_unicode_str.py`; no counterexample was found.

`eval.equivalence.EquivalenceResult.counterexample` — the countermodel a
refuted `solver`/`auto` equivalence check returns — is documented more
explicitly as the accessible field a caller checks after a `False` verdict,
rather than something to be inferred from the surrounding prose; the field
itself is unchanged.

### Packaging — `requires-python` stays `>=3.10`

Raised explicitly because a consumer building on the span layer asked: no,
it does not move. Nothing in this release's new surface —
`parse_with_spans`, the path-keyed `SpanMap`, `replace_at`/`node_at`, the
span-capturing Lark transform — reaches for anything newer than what the
rest of the kit already assumes; frozen dataclasses, `typing.Tuple`/`Dict`
generics and ordinary recursion are all 3.10-safe. There was no technical
reason to raise the floor, so it was not raised.

## [0.22.0] - 2026-08-14

### `atp.clingo_backend` / `atp.minizinc_backend` / `semantics.asp_models` — a decision procedure for counting, and minimal models without the second-order detour

Two questions the kit's other 19 backends could not answer, both closed by
grounding to a real finite-domain solver instead of exporting to unsorted
classical FOL:

- **The counting fragment had no solver.** `Count` (∃≥n/∃≤n/∃=n) and
  `Cardinality` (`|{v : φ}|` as a term) are genuinely second-order for
  `to_z3`/`to_prover9`/`to_tptp`, which reject them outright. Over a *finite*
  structure they are plain counting, and `ClingoBackend`/`MinizincBackend`
  decide them directly — `#count` in ASP, `sum(...)` over `bool2int(...)` in
  MiniZinc — rather than the `expand_count` blow-up.
- **Minimal models went through a second-order detour.** `minimal_models`
  enumerates and filters in Python; `circumscription_entails_so` builds a
  second-order formula. `semantics.asp_models.asp_minimal_models` lets clingo
  enumerate every model at a given size natively and filters through
  `nonmonotonic.py`'s OWN `_circ_profile`/`_strictly_below` predicate rather
  than reimplementing minimality — sound by construction, since the two
  routes share one filter and can only ever disagree about which models
  clingo found.

New shared layer `atp.finite_domain` (`FiniteDomainProblem`, `fragment_check`,
`structure_from_solution`, `verify_model`) gives both backends one gate for
`unsupported` and one re-verification step: every countermodel is run back
through `evaluate_in_structure` against the refutation goal before it leaves
the backend, never returned unchecked.

That rule turned out to bite the very fragment it was meant to protect. The
first build could ground and solve a cardinality comparison but not CHECK it —
`semantics.model_eval` refused `Cardinality` outright — so the counting
fragment came back `ERROR`/`infra`: sound, and hollow at exactly the point
that justified the work. Three changes close it, and they are improvements to
the kit independent of any backend:

- **`semantics.model_eval` now evaluates `Cardinality`.** Over a finite
  structure `|{v : φ}|` is counting — the same insight that already makes
  `Count` native there, one level down at the term. A comparison switches to
  the arithmetic reading as soon as one operand is numeric; `_term_value`
  still answers with individuals and still refuses numeric terms, so the two
  notions of "term value" meet only in that one branch instead of being merged
  throughout. Counting respects the evaluation budget per individual.
- **`semantics.model_eval` now evaluates `Contrast`** as the conjunction its
  own docstring says it is ("concession is a discourse relation, not a
  truth-functional one; exports behave exactly like `And`") — an omission
  restored, not a semantics invented.
- **`fragment_check` now refuses `Function`.** `FiniteStructure` has no slot
  for a function interpretation, so a model containing one could never be
  checked back; the refusal is an honest `UNKNOWN`/`unsupported` naming the
  reason, instead of a late `ERROR`/`infra` that reads like a transient fault.
  Giving `FiniteStructure` function interpretations touches serialisation, the
  evaluator and every consumer — separate work, not a detail of a backend.

Also fixed, found by a test written against the implementation rather than
with it: `ClingoBackend` universally closed the negated conclusion but not the
premises. The ASP encoding reads a free variable in a constraint as implicitly
∀-bound; `evaluate_in_structure` does not. Encoder and checker were looking at
different sentences, so a premise like `P(a)` (single letters parse as
VARIABLES here) produced a correct refutation that then failed its own
verification. Both now share one closed sentence list.

Both backends are **refutation-only, by construction** — neither imports
`PROVED` from `atp.protocol`. FOL has no finite model property, so "no
countermodel up to `max_size`" is `UNKNOWN`/`bound_hit`, never a validity
proof — the same discipline `ModelFinderBackend` and `KripkeEnumBackend`
already follow. Registered in `atp.protocol`'s registry next to
`Cvc5Backend`, but deliberately **not** added to any `default_chain`: they
fill the same role as `modelfinder`, already in the FOL chain, and promoting
a stronger implementation into the default path is its own measured decision
(the `cvc5` precedent), not a side effect of adding the backend.

New optional extras: `[asp]` (`clingo>=5.6` — the solver ships in the wheel,
no separate install) and `[cp]` (`minizinc>=0.9`, plus a separate MiniZinc
CLI on `PATH`/`$UFK_MINIZINC` — `MinizincBackend` shells out like
`Prover9Backend`/`VampireBackend`, it does not use the Python bindings this
extra installs). Without either extra, the corresponding backend reports
`available() == False` and every existing backend is unaffected.

### `unicode_fol_kit.ilp` — structures in, a learning task out

The other end of the Prolog importer. `IlpTask` turns
`FiniteStructure` objects into the three files an ILP system reads (`bk.pl`,
`exs.pl`, `bias.pl`); `clause_to_formula` turns the learner's answer back into
a kit formula that can be model-checked against the very structures it came
from. No new dependency: the kit writes and reads text, the learner is the
learner's business.

The module exists because two encoding mistakes are easy to make, invisible in
the output, and both produce a hypothesis scoring **precision 1.00 that means
nothing**. Both were made building this kit's own pre-trial, and both are now
refused rather than written down as advice:

- **Example-local individual names** let a learner join across examples through
  a shared constant. Every individual is prefixed by its example, and the task
  is refused if two constants still collide — examples and individuals share
  one namespace, so `m1` with individual `a` collides with an example `m1_a`.
- **The example argument on every predicate** lets a learner introduce a second
  example variable and connect through it. It exists on the membership
  predicate alone, and `clause_to_formula` refuses, coming back, a clause where
  the example variable survives or a second example is named.
- Two consequences of the same reasoning: a **0-ary** background predicate
  would hold across every example at once, and a goal **not linked** to the
  example ranges over the whole fact base rather than over one structure.
  Both are refused, the second with the linkage propagating through positive
  goals only — `\+` binds nothing in SLDNF.

`check_separation` asks the question that has to come first: does the reference
definition actually separate the two example sets under the kit's own model
checker? If not, the task is broken and no learner's answer would have meant
anything. Undecided (`exhausted`) and vocabulary errors stay separate from
"decided the wrong way", because those call for different fixes.

An adversarial review of the package raised 23 findings, 13 of which survived
refutation and are fixed here — including two holes in the guarantees above
(an example name colliding with an individual constant; two structure symbols
folding to one Prolog functor and being silently merged) and one in the name
check itself: `re.match` with a `$` anchor accepts a trailing newline, so
`"m1\n"` passed as a legal atom while being the *same* atom as `m1` to Prolog.

### API reference: complete, and enforced

`docs/api.md` now lists **every** name in `unicode_fol_kit.__all__` and in each
subpackage's `__all__` — 368 top-level names and 182 subpackage-only ones,
grouped by what they are for rather than by module. The ~90 AST node classes
(`Box`, `Always`, `Tensor`, `LukImplication`, …) had lived only in the syntax
reference. `tests/test_api_reference_complete.py` enforces the claim in both
directions, so a new public name cannot ship undocumented and a withdrawn one
cannot linger on the page.

Rendering names that had never been rendered exposed the docstring faults that
go with them, all fixed here: ad-hoc `Fields:` blocks docutils reads as
definition lists (which breaks any inline literal that wraps to the next line),
`|{v : φ}|` read as substitution syntax, a bare `c_` read as a link target, an
unescaped `*` in prose, a literal followed immediately by a letter, and two
first sentences autosummary cuts inside a literal. Ten dict registries and
naming maps had no documentation at all and were rendering `dict.__doc__`; they
now carry `#:` comments at their definition site and are listed there.
`conf.py` gains `autosummary_filename_map` for the seven name pairs that differ
only by case (`Would`/`would`, `Line`/`line`, …) and therefore collide as
filenames on a case-insensitive filesystem — a build that was clean on Linux
and broken on Windows. A clean docs build is at **0 warnings**.

Documentation — **the shipped-but-invisible subsystems now have pages.** An
audit against `__all__` found 371 public names and 106 of them in the API
reference; the gap was not evenly spread but concentrated in whole subsystems
that had neither a guide page nor an API entry. HETS was the starkest: a Docker
binding, a REST client, a prover backend and a comorphism bridge, undiscoverable
for anyone reading the docs.

- New **{doc}`guide/interoperability`** — the importer/exporter family under one
  rule ("an importer inverts naming, and refuses what it cannot read"): the
  dialect table, why Prolog is deliberately not in `parse_any`'s auto-detection,
  the two readings of a Prolog clause, negation-as-failure as an opt-in, the
  by-name refusals, the CASL round trip, HETS (discovery, client, backend, the
  *discovered* `hets:<Name>` edges), and the ILP round trip with the two
  encoding traps that produce a perfect score and mean nothing.
- New **{doc}`guide/batch-checking`** — `check_definitions` and
  `StructureCache`: the data-becomes-a-row / configuration-raises contract, the
  status table (including why `exhausted` is not `False`), the four-field cache
  key with the reason for each field, and resumption.
- `docs/api.md` gained the entry points that had none: Prolog, CASL in both
  directions, the chemistry layer, the **backend protocol** (the extension point
  for a prover the kit has no backend for), `batch_decide`/`check_definitions`,
  the evaluation functions, plus `hets`, `comorphism` and `drt` in the module
  list.

Every example on both new pages is executed, not asserted: 15 blocks run, 3
skipped as needing Docker, 0 failing. Rendering the newly listed modules also
exposed reStructuredText faults in docstrings that had never been rendered —
block quotes where lists belonged, unpaired literals, a title underline too
short. Those are fixed across ten modules, and a clean docs build is now at
**0 warnings** (it was 9 before this work).

## [0.21.0] - 2026-08-13

Added — **`fol.parse_prolog_clause` / `parse_prolog_program` / `load_prolog`**,
the missing leg of the importer family (TPTP, Prover9, SMT-LIB, LaTeX, CASL —
and now Prolog/Datalog). Its immediate use is reading back what a rule learner
produces, so an induced clause can be model-checked, proved with, exported to
TPTP or compared against a reference instead of eyeballed.

Two things it refuses to decide for you:

- **Which reading.** `h(A) :- b(A, B).` is either `∀a∀b (B(a,b) → H(a))`
  (`mode="clause"`, the standard logical reading) or the CONDITION alone,
  `∃b B(a,b)` with the head's variable free (`mode="body"` — what a class
  definition is). Different formulas; the caller says which.
- **Negation as failure.** `\+ G` means "not derivable", which is `¬G` only
  under the closed world assumption on a stratified program. Refused unless
  the caller passes `negation_as_failure="classical"` and thereby asserts it.

The cut, if-then, `is`, `=..` and list terms are refused **by name** — a
parser that quietly dropped a cut would change what the program means. Naming
is inverted on import like TPTP's (`carbon(A)` → `Carbon(a)`), folding only
the FIRST character, so ChemLog's `bSINGLE` survives as `BSINGLE` rather than
collapsing to `Bsingle`. Prolog is deliberately NOT added to `parse_any`'s
auto-detection: `p(a).` is ambiguous with several other dialects, and silent
misrouting is the failure this kit exists to avoid — ask for it explicitly.

Added — **`eval.check_definitions` + `chem.StructureCache`**: the layer a
campaign runs on. `score_definition` answers "how good is THIS definition";
this answers "run K definitions over N molecules and write down everything
that happened", and its contract is drawn along one line: **is this a property
of the data or of the configuration?** Data becomes a ROW — an unparseable
SMILES, a definition mentioning a predicate no structure interprets, a budget
that ran out — so one bad molecule in 200 000 never costs the other rows.
Configuration (RDKit missing, unknown `naming`, unwritable results path) fails
loudly *before the first molecule*. Rows are flushed per definition, and
`resume=True` reads back what a killed run already wrote instead of redoing
it. An exhausted budget is its own status with `holds=None`, never a `False`.

`StructureCache` is what makes the inner loop cheap: the structure does not
depend on the formula, so K definitions over N molecules build N structures,
not K·N. Measured with the new runner, 4 definitions × 60 molecules:
**1860 → 8000 checks/s, a factor of 4.3** at a 0.958 hit rate. Failures are
cached too — a SMILES RDKit refuses is refused identically next time.

Fixed — **the structure cache key now carries `naming`** (BREAKING for a
caller that builds its own keys: the tuple grew from three fields to four —
`(smiles, naming, aromatic, computed)`. Passing a plain `dict` as
`structure_cache` and letting the kit key it needs no change). It was
`(smiles, aromatic, computed)`, correct only because
`eval.datasets.c3po` hardcodes `naming="chemlog"` — an invariant nothing
enforced. A shared campaign-wide cache breaks it: `mcp.chem_tools.
molecule_to_structure` exposes `naming`, and `"paper"` spells the single bond
`singleBond` where `"chemlog"` spells it `bSINGLE`, so a cross-answered
request would report every predicate as uninterpreted. The key is now the full
option tuple, and `c3po`'s sentinel for a refused SMILES is the same class as
the cache's, so neither module's `isinstance` check can miss the other's
cached failures.

Added — **`eval.minimal_model_size(..., all_different=True)`**: the generality
analysis under ChemLog's own convention, and the reason it was needed is the
measurement it replaces. Under plain FOL semantics a definition built only
from ∃, ∧ and ∨ — what an LLM writes for a chemical class — is satisfied by a
ONE-element structure interpreting every predicate as universally true,
whatever the definition says. Measured over the 367 learned definitions of the
published run: **265 of 366 parseable ones are provably in that fragment**, so
the number was constant 1 and separated nothing. Under the convention it
measures what the definition actually demands: how many DISTINCT individuals
must exist.

Two implementation points carry the feature. It is a **formula
transformation**, not a search-time switch — the finder evaluates with
`semantics.tarski.satisfies`, which has no all_different reading, so the
implicit distinctness is written out as ≠ atoms, placed INSIDE each binder
(conjoining them to the formula as a whole leaves the variables free, and a
free variable reads as universally quantified: "every individual differs from
itself", i.e. every formula unsatisfiable). And it is answered in **closed
form** for the fragment where that is provable — `n` existentials over a
negation-free, comparison-free matrix have a smallest model of exactly
`max(n, 1)` individuals, proof in `_closed_form_size` — because a class
definition binding two dozen atoms is not reachable by enumeration at all.
The closed form is checked against the search it replaces, on formulas small
enough for both.

Added — **`fol.repair_formula`**, the repair layer for LLM output written in
the kit's OWN surface syntax, plus the matching `repair_formula` MCP tool
(29 tools now). `fol.repair_tptp_formula` has covered the three recurring
LLM syntax-failure classes in TPTP since 0.20.0; carrying them to the unicode
dialect gives three different answers, and that difference is the feature:

- **Biimplication brackets** have no analogue. The grammar puts
  ↔/→ below ∧/∨, so `P(x) ↔ A(x) ∧ B(x)` is unambiguous, and
  `to_unicode_str` re-emits exactly those brackets — nothing to normalise on
  either side. What the grammar refuses instead, `A ∧ B ∨ C` mixed at one
  level, is **reported and never repaired** (`"mixed_connectives"`): the two
  readings are different formulas, and bracketing one would throw away the
  property that makes this dialect worth generating in.
- **Invalid names** are renamed, not quoted — the unicode grammar has no
  quoting mechanism at all. The rename goes through `sanitize.NameMapping`,
  so it is invertible (`names`, and the caller's own mapping for run-wide
  consistency), unlike a plain camelCase fallback. A legalised name can never
  collide with a symbol already in the text, and a rewrite that does not make
  the input parse is discarded whole rather than half-applied.
- **Free variables** are handled identically, by calling
  `tptp_repair`'s own two fixes rather than reimplementing them, so the two
  paths cannot drift.

## [0.20.0] - 2026-08-13

Added — **finite structures and model CHECKING** (`semantics.structures` +
`semantics.model_eval`). The kit could already SEARCH for a model; it can now
evaluate a sentence in a structure that is GIVEN — the direction structured
real-world data actually needs. `FiniteStructure` carries a domain, extensions
keyed by `(name, arity)`, and **computed predicates**: symbols decided by a
callable rather than a stored extension, which is how properties that are
decidable on a finite structure but not first-order definable over it
(connectivity, ring membership) enter without leaving first-order logic.
Indexing (`individuals_with`, `neighbors`) is part of the contract, because
iterating a quantifier over "the oxygens double-bonded to this carbon"
instead of over the whole domain is the difference between a millisecond and
a timeout. `graph_to_structure` builds one from any labelled graph.
`evaluate_in_structure` / `evaluate_detailed` evaluate the AST **directly** —
no prenex form, no CNF: negated existentials search for a witness and stop,
disjunctions short-circuit, and the counting quantifier is counted rather
than expanded. (Those three are not micro-optimisations: the published
ChEBI2FOL evaluation documents its checker's PNF/CNF requirement as the
*source* of two of its three timeout classes.) `all_different` is offered as
an explicit semantics switch, budgets exhaust into an honest `None` rather
than a `False`, and an uninterpreted symbol raises instead of silently
reading as false. Differentially tested against the kit's own `satisfies`.

Added — **`unicode_fol_kit.chem` — molecules as finite FOL structures**
(optional `[chem]` extra for RDKit; the signature, structure and evaluator
layers are RDKit-free). `mol_to_structure` turns a SMILES or RDKit molecule
into a structure over ChemLog's signature — heavy atoms as individuals, atom
types / hydrogen counts / charges as unary predicates, bonds as symmetric
binary relations, net charge as 0-ary — reproducing the worked ethanol
structure from the ChEBI2FOL paper exactly, plus ten computed predicates
(`in_ring`, `in_ring_of_size_3..8`, `aromatic`, `same_fragment`,
`carbon_connected`). `CHEMLOG_SIGNATURE` makes `api.check` report unknown
predicates and arity errors against that vocabulary. **`chem.interop`** is
the bridge that makes the two halves meet: TPTP inverts the kit's case
convention, so a formula imported from ChemLog TPTP arrives as `C/1` where
the structure carries `c/1` — `parse_chemlog_tptp` renames the chemical
vocabulary back, with the mapping's **injectivity checked at import time**
(a non-injective renaming would merge two predicates into one, the same
soundness trap `atp.tptp_ncl` guards against). Verified end to end: ChemLog's
amide-bond axiom holds of glycylglycine and fails on ethanol, sub-millisecond.

Added — **`fol.tptp_repair` — syntax repair that costs no generation
attempt.** The three failure classes measured in the ChEBI2FOL evaluation
(89 of 136 failed classes) are handled: an unbracketed biconditional is
re-emitted fully bracketed (the kit's parser already reads it with the
correct precedence, so the rewrite is meaning-preserving — asserted by an
equivalence test, not by claim); a predicate name that begins with a digit or
carries punctuation is single-quoted per the TPTP standard, which preserves
the full chemical name *including* locant prefixes that a camel-case
sanitisation would discard; free variables are REPORTED, and only closed on
explicit opt-in — silently binding them would change what the author claimed.

Added — **`fol.simplify_check` — the anti-bloat pass.** Under the
`all_different` convention, pairwise inequalities between separately
introduced existential variables are redundant; `simplify_for_checking`
removes exactly those (never inequalities involving constants or
universally bound variables, and never under standard semantics).
`count_from_existential_chain` recognises the "n distinct witnesses of one
predicate" pattern and contracts it to `∃≥n`, refusing whenever the variables
carry further structure; `expand_count` goes back for backends without
counting. Both directions are z3-verified as equivalent. On the published
40-variable / 780-inequality example this removes all 780 literals.

Added — **`eval.theory_check` — deductive checks over a set of DEFINITIONS.**
Where the existing verbs decide one formula, this decides a vocabulary:
`dependency_graph` / `find_cycles` (a circular definition fixes nothing and
must be reported, not evaluated), `unfold` (substitute defined predicates
down to primitives — the part that makes the background axioms right),
`check_satisfiable` (an unsatisfiable definition is a classifier that
silently returns zero hits forever), and `check_subsumption`, which answers
`Def(sub) ⊨ Def(sup)` over the backend chain. The last one is the point:
where a single prover reports only "proved / not proved", a `"refuted"`
verdict here always carries a **countermodel** — a concrete structure
satisfying the subclass and violating the superclass, which says *why* — and
`"unknown"` is never reported as `"refuted"`. `check_theory` aggregates into
a report that keeps proven defects and open questions strictly apart.

Added — **`eval.generality` — is this definition too easily satisfied?**
`minimal_model_size` finds the smallest finite structure satisfying a
definition, which turns over-generality into something measurable *without
any dataset*: a class whose real members have fifty atoms but whose
definition is satisfied by a three-atom structure is under-constrained, and
that is visible before a single membership check runs. Deliberately
calibrated as an indication, not a verdict — the report only judges against
an `expected_min_size` the caller supplies, and never invents a threshold of
its own. `is_vacuous_specialisation` catches the subclass definition that is
logically equivalent to its superclass (specialising nothing), and
`strictly_stronger` separates a real specialisation from an undecided one,
combining the two entailment directions in genuine three-valued logic.

Added — **`eval.datasets.c3po`** — the first adapter whose gold is not a
formula but an **executable membership decision**: `score_definition` model-
checks a candidate definition against real molecule structures and reports
the confusion matrix — with budget exhaustion and evaluation errors kept in
their own categories rather than quietly counted as negatives, which is the
difference between a metric and a flattering metric.

Added — **`mcp.chem_tools` — six chemistry tools** on the MCP server
(28 tools total): `molecule_to_structure` (see what the definition is being
checked against, instead of guessing), `check_molecule` / `check_molecules`
(three-valued, batch-safe), `explain_molecule_failure` (which conjunct fails,
which atoms and bonds exist — the counterexample-explanation component the
ChEBI2FOL evaluation names as missing), `simplify_definition`, and
`chemical_signature` (the permitted vocabulary, so the model need not guess).

Added — **`mcp.syntax_spec` + the `get_syntax_spec` tool** (server: 22
tools at that point, 28 after the chemistry tools). Eight retrievable topics — naming conventions, operator precedence,
quantifier scope, the counting quantifier, dialect selection, the chemical
signature, and a catalogue of measured LLM failure modes with fixes. **The
spec cannot drift from the parser**: every example it serves is parsed with
its declared dialect and compared to its advertised rendering by the test
suite, and facts derivable from live objects are read from them. Every parse
failure the server returns now carries a `spec_topic`, so a generate → fail →
look up → regenerate loop closes without the grammar living in the prompt —
which matters when the generating model pays for prompt tokens on thousands
of classes.

Added — **`unicode_fol_kit.prob` — exact probabilistic logic (no sampling,
no floats)**: `prob.nilsson.entailment_bounds` computes Nilsson-style
probability-interval entailment over propositional formulas as an exact
linear program (Z3 `Optimize`, `Fraction` in and out, conditional
constraints in Nilsson's linear form, quantifiers refused loudly —
classical entailment falls out as the bounds-collapse-to-(1,1) corner
case); `prob.distribution.query` implements Sato/ProbLog distribution
semantics over definite logic programs (independent ground `ProbFact`s +
`∀`-quantified definite-clause rules), summing exact total-choice weights
via forward-chained least Herbrand models, with correctness-preserving
dependency-cone pruning and honest exponential-blow-up brakes
(`max_atoms` / `max_choice_facts`). Exposed over MCP as
`probability_bounds` / `probability_query` (JSON probabilities read
decimally — `0.7` means 7/10, never the binary float artefact). 53
hand-checked tests (+4 through the MCP layer).

Added — **four guide pages for the layer this release adds**, each example
executed against the built package rather than written from memory:
`model-checking` (finite structures, computed predicates, molecules as
structures, and the measured cost of the counting quantifier — 108979 → 8
evaluation steps on the same six-carbon query), `verification` (repair,
definition sets, satisfiability, subsumption with countermodels, minimal
models, vacuous specialisation), `probabilistic` (Nilsson bounds vs
distribution semantics, and why one returns an interval and the other a
number) and `mcp` (the tool inventory and the self-correction loop). The API
reference gained the matching entry points; `docs/index` names the four in
its opening.

Fixed — **`diagnose` returned the least informative of the competing parse
errors, and no topic at all.** `api.repair`'s suggestion took `errors[-1]`,
but errors arrive one per candidate dialect in detection order and the
specialised dialects at the end of it are the ones that give up EARLIEST on
ordinary input — so for `A ∧ B ∨ C` the suggestion was lambek's "Invalid
predicate 'A'" rather than the mixed-connective diagnosis seven other
dialects had reached. It now picks the message from the dialect that read
furthest (shared helper, also used by the MCP topic routing), and the MCP
`diagnose` tool carries `spec_topic` like every other failing tool, so the
loop it exists to drive can actually close.

Fixed — **a mixed-connective rejection was diagnosed as a naming error**, in
the message and in the MCP correction loop. The kit's unicode grammar puts
∧, ∨ and ⊕ on one level and refuses `A ∧ B ∨ C` rather than resolving it by
precedence — deliberately, since the two readings are different formulas and
in the linear and fuzzy modes there is no agreed precedence to resolve it
with. But the lexer stops with the *predicate* `B` in hand, and the message
read "Invalid predicate 'B' … Expected pattern: `[A-Z][a-zA-Z0-9]*`" — a
claim that is simply false, `B` matches that pattern. The mixing hint is now
attached whatever the preceding token was, and the naming wording (with its
"expected pattern") is reserved for characters that really are name
problems. In `mcp.server`, `spec_topic` sent the same failure to the
`naming` rules, a dead end: every name in the formula is already well
formed, so a generator would rename them and be rejected in the same place.
Routing now weighs how FAR each dialect got against how MANY agree — the
dialects that never reach the offending connective no longer outvote the
ones that did, and a single dialect that happens to consume the whole string
no longer outvotes six that agree on the real cause. `A ∧ B ∨ C` routes to
`operators`, `∀ P(x)` to `quantifiers`, and the errors catalogue gained the
mixed-connective class with the fix (bracket, do not rename).

Fixed — **Tier-3 adversarial review (9 confirmed findings, all fixed with
regressions)**. Two soundness cores: (1) the resolution prover's
shared-instance SELF-paramodulation shortcut was UNSOUND (it dropped both
the consumed equation and the target literal from one instantiation —
``{a=b ∨ ¬P(b)}, {P(a)}`` "refuted" a satisfiable set) — removed from the
prover AND from the independent checker's rule vocabulary (a clause
paramodulating into itself goes through the sound renamed-copy cross path;
an external derivation claiming ``self_paramodulate`` is now rejected, not
re-derived); (2) the tableau checker never verified that a step's principal
formula is actually ON the branch it extends, so a fabricated proof could
"decompose" an invented contradiction and close on its own components —
branch-membership is now enforced for every step and every β split (two
fabrication attacks pinned as tests). Contracts: `parse_casl_spec` gained a
post-parse usage-conformance pass (undeclared symbols and declared-vs-used
arity mismatches now refuse loudly instead of returning a self-inconsistent
CaslSpec) and discloses the third round-trip exception (a SortedQuantifier
at exactly `default_sort` collapses to a plain Quantifier — the CASL text
cannot tell them apart); `to_casl_spec` validates `default_sort` itself
(the union-find fallback emitted an unchecked caller string into the
`sorts` line); the MCP `truth_table` tool no longer leaks a raw
NotImplementedError on modal/fuzzy input and `probability_bounds` refuses
JSON booleans as probabilities; the resolution checker's unknown-rule
message enumerates its actual rule vocabulary (generated, so it cannot
drift again).

Added — **tableau proof objects + an independent tableau checker**.
`prove_tableau_detailed` records a `TableauProof` (root formulas, the
α/β/γ/δ rule tree with node IDs, γ instantiation terms and δ witness
constants explicit per step, each closed branch's closure pair) alongside
the EXISTING search — the algorithm itself is untouched and the detailed
route provably agrees with `prove_tableau`. `atp.tableau_check
.check_tableau_proof` verifies every step independently: its own rule
dispatch, its own capture-avoiding substitution (`fol.nodes.substitute`,
not the producer's), its own branch-local δ-freshness check, full-closure
accounting (no open branch slips through) — the third independent proof
checker after resolution and Twee. The `"tableau"` backend's PROVED
Verdicts now carry the checkable proof dict. 46 hand-checked tests
including an eight-way tamper suite.

Changed — **the resolution prover learned equality: sound paramodulation,
reflexivity resolution, and demodulation**. `alice = bob, P(alice) ⊨
P(bob)` and function congruence are now provable WITHOUT hand-supplied
equality axioms (`=` previously was an ordinary uninterpreted predicate
for this prover — the documented guide example flipped from False to
True and was updated). Ordering: term size with lexicographic
tie-breaks, checked on concretely substituted terms (so no
substitution-closure subtlety); demodulation only rewrites under a
strict orientation and is recorded as its own proof step, never
silently. The independent checker gained matching `paramodulate` /
`self_paramodulate` / `reflexivity` / `demodulate` rules that re-derive
every unifier, position, and orientation from scratch. Honest limits in
the module docstring: unconditionally sound, NOT complete for equational
logic — the didactic core stays didactic; E/Vampire/cvc5/Twee remain the
heavy equipment. 43 new tests + 6-way tamper suite; all 316 dependent
tests green.

Added — **CASL import + DOL libraries — the CASL route becomes a
round-trip**. `fol.casl_import.parse_casl_spec` inverts `to_casl_spec`:
a hand-rolled recursive-descent parser (lazy lexer, real precedence
climbing) for the emitted CASL fragment plus a tolerant superset
(singular/plural declaration keywords, `%%` comments, multi-variable
quantifiers, optional `end`), returning `CaslSpec(name, signature,
axioms, conjectures)` with the round-trip contract
`parse_casl_spec(to_casl_spec(fs)).axioms == fs` tested across the
classical/many-sorted fragment; everything outside (partial functions,
subsorting, free/generated types, structuring, attributes) raises
`CaslImportError` with a line number. Documented irrecoverables: 0-ary
ops always reconstruct as `Constant`, and `Xor` comes back as
`Not(Iff(…))` (the export is textually identical). `hets.dol.to_dol_library`
emits multi-spec DOL libraries (`then`-extension structure, `%implied`
goals) — live-verified against a HETS server: the development graph
shows both named nodes and SPASS proves an extension node's implied
goal (emission only; no DOL parsing, same cut as T2). 64 tests
(62 offline + 2 `hets_live`).

Added — **MCP error-analysis wave: twelve more tools (nine →
twenty-one, the two probabilistic tools above included)**. The
server now also exposes `normalize` (nnf/pnf/cnf/dnf/canonical are
equivalence-preserving, `tseitin_cnf` declares itself EQUISATISFIABLE and
`skolemize` satisfiability-preserving via the `semantics` key; `is_horn`
rides along), `render` (unicode / TPTP / Prover9 / LaTeX / bare CASL /
versioned-JSON envelope / deterministic English), `detect_dialect`
(nomination list + what actually parsed), `compare_formulas` (the
per-pair error-analysis breakdown: structural / canonical / vocabulary-
aligned match, the renamed prediction, the graded equivalence verdict,
and a per-namespace `Name/arity` symbol diff), `score_batch`
(`compute_fol_metrics` over aligned lists), `check_consistency` (is the
SET satisfiable — fresh-atom contradiction encoding, model witness with
English gloss / refutation verdict / honest `None`), `get_signature`
(inferred `Signature` dict, ready to feed back into
`check_formula`/`diagnose`), `truth_table` (classical/K3/LP by full
enumeration, quantifiers and >4096-row tables refused loudly),
`drs_to_fol` (box/SBN discourse → provable FOL, optional
accessibility-respecting pronoun resolution), and `list_translations`
(comorphism edges, `hets:<Name>` bridges included after a refresh). All
parse failures keep the ONE `{"ok": False, "argument": …, "errors": […]}`
shape; 30 new hand-checked tests (46 total for the server).

Added — **the Tier-0 package of the NL→logic infrastructure roadmap**: a
seven-verb facade, a uniform prover protocol, versioned serialisation, and
repository hygiene. Everything is additive; no existing signature changed.

- **`unicode_fol_kit.api` — the seven-verb facade** (namespaced on purpose:
  `api.prove` must not shadow the resolution prover's top-level `prove`):
  `parse_any` (dialect detection over unicode-MSFL modes / TPTP annotated+bare /
  LaTeX / Prover9 / SMT-LIB, never raises, records every attempt's error),
  `check` (well-formedness plus optional signature conformance with
  did-you-mean suggestions), `equivalent` (re-export, see below), `prove` /
  `countermodel` (backend chains, see the protocol), `repair` (a
  diagnose→suggest→fix generator whose `fixer` callback the caller's LLM
  supplies), and `translate` (comorphism registry). All result objects carry
  JSON-compatible `to_dict()`. The module documents the API stability policy
  (additive-only within a minor line).
- **`atp.protocol` — one `Verdict` over every decision route.** Semantic
  `status` (proved / refuted / unknown / error) with a separate `reason` axis
  (`timeout` / `bound_hit` / `incomplete` / `unsupported` / `infra`), SZS
  ontology values, wall-time and provenance. Nine backends registered at
  this layer's introduction — the kit's OWN calculi and semantic searches as
  first-class citizens (`tableau`, `resolution`, `modelfinder`,
  `modal-tableau`, `qml`) next to the solver and prover routes (`z3` — the
  bundled SMT solver — plus the separately-installed `isabelle`, `prover9`,
  `vampire`); the Tier-1 wave below brings the registry to twelve with
  `cvc5`, `kripke-enum`, and `leo3`. Loud availability contract: unknown
  name → `ValueError`, known-but-missing → `BackendUnavailable`, never a
  silent skip; an in-backend crash becomes an ERROR verdict so batch runs
  record failures instead of dying. The default chains never run the
  minutes-per-call Isabelle route implicitly.
- **`eval.equivalence` — graded equivalence for NL→FOL scoring.**
  `equivalent(prediction, reference, method=…)` runs the ladder exact →
  canonical → predicate-aligned → solver; the solver level is TRI-STATE
  (`True` / `False` + counterexample / `None`), deliberately unlike
  `formulas_are_equivalent`, which collapses unknown to False. Modal formulas
  route through `modal_decide` (with Kripke witnesses) and fall back to the
  sound-incomplete QML embedding, whose "not proven" is never reported as a
  refutation.
- **`eval.predicate_match.align_symbols` / `aligned_exact_match` — AST-level
  symbol alignment** with the three guarantees the lexical matcher cannot
  give: separate predicate/function/constant namespaces, arity-awareness, and
  an injective, capture-free greedy assignment (two prediction symbols never
  merge; a symbol is never renamed into a name the prediction already uses).
- **`fol.serialize` — versioned JSON envelope**: `serialize` / `deserialize` /
  `SCHEMA_VERSION` wrap the unchanged `to_dict()` node format in
  `{"schema_version": 1, "root": …}`; future versions are rejected loudly,
  bare pre-envelope dicts keep loading. The CLI's `--to json` now emits the
  envelope (its only breaking surface change, listed here deliberately).
- **`comorphism` — the kit's translations as a composable registry** (the
  HETS idea, native Python): `standard_translation` (modal→fol), ALC→modal-K,
  ALC→FOL, dependence→ESO as named edges with BFS path composition and
  per-edge convention notes; `register_comorphism` for third-party edges.
- **Repository hygiene**: `.github/workflows/tests.yml` runs the fast suite
  (`pytest -n auto -m "not isabelle_live"`) on every push/PR across Python
  3.10–3.13 on Linux plus a Windows leg; README carries the badges;
  `CITATION.cff` makes the repo citable.

Added — **the Tier-1 wave**: three new prover backends, the SZS/TSTP reading
layer, batch/portfolio evaluation, dataset adapters, countermodel
explanations, supervaluationism, and Manchester OWL syntax. Additive
throughout, with two deliberate behaviour upgrades called out below (the
default chains and the `vampire` backend).

- **`atp.cvc5_backend.Cvc5Backend`** (`"cvc5"`, optional extra
  `unicode-fol-kit[cvc5]`): a second, fully independent SMT decision procedure
  for classical FOL, fed through the SAME `to_z3()` translation Z3 already
  trusts (via canonical SMT-LIB2 text, so the two translations can never
  drift apart). When the extra is installed, `default_chain("fol")` becomes
  `("z3", "cvc5", "tableau", "resolution", "modelfinder")` — the one
  documented availability-dependent chain member; without it the chain is
  unchanged.
- **`atp.kripke_enum`** — bounded exhaustive enumeration of finite Kripke
  models against the kit's OWN `satisfies_modal` evaluator:
  `modal_enum_search` (three-way honest: countermodel / exhausted / budget
  hit), `modal_enum_countermodel`, and the refutation-only `"kripke-enum"`
  backend. **This closes the temporal-refutation gap**: `Ⓕ P → P` (invalid)
  was previously "unknown" on every route — the labelled tableau has no rule
  for the temporal closure operators and the QML embedding is proof-only —
  and is now REFUTED with a two-world witness. `default_chain("modal")` is
  now `("modal-tableau", "kripke-enum", "qml")`, and `api.countermodel`'s
  modal chain gained the same member.
- **`atp.tstp`** — the TPTP-family result reader: `extract_szs_status`,
  `szs_to_verdict_fields` (SZS → the protocol's status/reason axes), and
  `parse_tstp_derivation` (annotated `fof`/`cnf` output → a `TstpDerivation`
  proof DAG).
- **`vampire` backend upgraded to the SZS route** (behaviour change, strictly
  more informative): `szs_status` is Vampire's own status line verbatim, a
  `CounterSatisfiable` answer is an honest REFUTED (previously collapsed into
  "unknown"), and a PROVED verdict carries the parsed TSTP derivation in
  `proof`. The underlying plumbing (`check_entailment_vampire_detailed`,
  passing `--proof tptp`) is additive next to the unchanged boolean
  `check_logical_entailment_vampire`.
- **`atp.tptp_ncl.to_tptp_ncl` + `atp.leo3_backend.Leo3Backend`** (`"leo3"`,
  `$UFK_LEO3` + `java`): NXF export of the mono-modal alethic propositional
  fragment (frames K/T/S4/S5, syntax verified against the current TPTP NCL
  documents) and the Leo-III adapter reading results back through `atp.tstp`.
  Out-of-fragment formulas are `UNKNOWN/"unsupported"` — a malformed NXF file
  never reaches the subprocess.
- **`atp.portfolio.portfolio_prove`** — run several backends CONCURRENTLY on
  one goal (processes, capped at 8): first definitive verdict wins,
  `require_agreement=n` collects n agreeing backends, and a PROVED/REFUTED
  split between two backends is a soundness alarm reported as an ERROR
  verdict — never auto-resolved.
- **`eval.batch.batch_decide`** — the campaign runner: content-addressed
  verdict cache (keyed over the versioned serialisation, backend list,
  timeout and options), process parallelism (jobs ≤ 8), JSONL results,
  per-task error isolation.
- **`eval.datasets`** — benchmark adapters with a shared `DatasetExample`
  shape, machine-readable `DATASET_INFO` (source, license, field schema), a
  curated `known_bad_ids` mechanic, and `audit_examples` (does every gold
  formula parse and validate?). Eight adapters, every upstream schema
  verified at the primary source: FOLIO, MALLS, **GROVES**, WillowNLtoFOL,
  ProntoQA (Logic-LM rendering, including `parse_logic_program` — the
  Logic-LM DSL compiled to kit ASTs — and `solve_example`, deciding each
  example end-to-end via `api.prove` against the gold answer), ProofWriter
  (no FOL gold; the CWA/OWA-vs-classical-entailment caveat is documented
  prominently), LogicNLI (upstream structured logic annotation preserved in
  `meta`, honestly not presented as FOL strings), and ProverQA (gold FOL
  loaded verbatim although its naming convention is the opposite of this
  kit's grammar — never silently rewritten). AR-LSAT, LogicalDeduction and
  FraCaS were verified and deliberately omitted (no logic annotations exist;
  the package docstring records the reasons). Measured honesty findings
  shipped with the adapters instead of being smoothed over: WillowNLtoFOL
  parses ~98.8% under this kit's grammar (three real defect classes pinned
  by tests); ProntoQA's GPT-4-generated DSL reproduces its own gold answer
  on only 76/100 sampled rows (both mismatch classes cited by row id).
- **Per-dataset import dialect grammars** — gold FOL whose notation the kit's
  own grammar refuses is now parsed at import time with a DEDICATED grammar
  per dataset and re-emitted in kit notation, instead of being lexically
  rewritten or left unusable. ProverQA (previously 0% kit-parse): a Lark
  grammar for its snake_case-predicate / Capitalised-constant notation with
  an injective, recorded renaming (`HasExperiencedHeartbreak(brecken)` from
  `has_experienced_heartbreak(Brecken)`; collisions and constant→variable
  degradations refuse loudly) — the fixture now audits 8/8 well-formed, and
  `proverqa.solve_example` reproduces 7/8 gold answers end-to-end via
  `api.prove` (the 8th is the documented upstream predicate-name typo, where
  the classical verdict is honestly "Uncertain"). WillowNLtoFOL: a repair
  grammar for its measured ~1.2% tail — the NLTK/textbook precedence reading
  (∧ over ∨, the convention Willow's own nltk-based filter used) for
  unparenthesised connective mixes, NFKD + case repair for out-of-class
  predicate names (`iOS`→`IOS`, `Café`→`Cafe`); the ~98.8% that already
  parse stay byte-for-byte verbatim, and only the genuine arity defect
  remains visible to `audit_examples`. Originals and changed-name mappings
  always land in `meta`; `convert_fol=False` restores raw pass-through.
- **`load_proofwriter_structured` — FOL GENERATED from ProofWriter's own
  symbolic annotations.** The structured OWA distribution (mirrored complete
  at `hitachi-nlp/proofwriter_processed_OWA`) ships RuleTaker triple/rule
  representations next to every sentence; `parse_proofwriter_representation`
  translates them deterministically (attribute triples → unary atoms,
  relation triples → binary atoms, polarity → ¬, `something`/`someone`
  placeholders → universally quantified variables) — no LLM, no NL
  heuristics. One example per question, `meta["fol_generated"]` marks the
  kit-generated origin, and `solve_structured_example` decides each
  question with a CALLER-CHOSEN ATP (`prove_kwargs` go verbatim to
  `api.prove`) under either reasoning assumption: `semantics="owa"` runs
  the entailment cascade (True ⇔ premises ⊨ q, False ⇔ premises ⊨ ¬q,
  Unknown otherwise — reproduces the OWA labels 24/24 on the real fixture),
  and `semantics="cwa"` runs two-valued CLOSED-MODEL CHECKING — the closed
  model is COMPUTED exactly by LOCALLY stratified forward chaining over
  the grounded theory (perfect-model semantics: rules with negated bodies
  get their standard negation-as-failure reading, the negatively-tested
  GROUND ATOM fully fixpointed in a lower stratum first — ground-level
  strata rather than predicate-level, which real ProofWriter theories
  require: `¬Likes(mouse, dog) → Likes(dog, rabbit)` cycles through
  negation on the predicate graph but not on the ground graph), the query
  is evaluated compositionally in it (¬q true iff q not in the model; ∀/∃
  over the theory's constants), and on definite theories every queried
  atom is cross-checked against the caller's chosen ATP (least model ⟺
  classical entailment there; a definitive disagreement raises a soundness
  alarm). Only a GROUND cycle through negation (not even locally
  stratifiable) or a theory deriving an atom both positively and
  negatively (inconsistent under CWA) is refused. The CWA route is
  verified against the original AllenAI release
  (`proofwriter-dataset-V2020.12.3.zip`, whose per-question schema the
  loader reads unchanged): the first 100 theories of
  `CWA/depth-2/meta-dev.jsonl` reproduce 1078/1078 gold answers across
  all four configs (AttNoneg/AttNeg/RelNoneg/RelNeg), and
  `tests/fixtures/proofwriter_cwa_mini.jsonl` pins two of those real rows
  (one definite, one NAF theory needing local stratification) as a 24/24
  regression fixture. All three dataset solvers (`proverqa.solve_example`,
  `prontoqa.solve_example`, `proofwriter.solve_structured_example`) take
  `on_indefinite="label" | "abstain" | "raise"` controlling how a
  NON-DEFINITIVE prover outcome (unknown/error — timeout, hit bound) is
  interpreted when neither entailment direction was proved: `"label"`
  (default) scores the dataset's uncertain label; `"abstain"` labels it
  ONLY when both directions are definitively refuted (underdetermination
  established by countermodels) and returns `predicted=None` otherwise, so
  a prover timeout can never be silently credited as a correct
  "Unknown"/"Uncertain"; `"raise"` turns an indefinite leg into a
  `ValueError` for hole-free pipelines.
- Willow license note: explicit usage permission for the
  GROVES/unicode-fol-kit use was obtained from the Willow authors (recorded
  in the adapter next to the still-flagged CC-BY-4.0 vs CC BY-NC-ND 4.0
  card discrepancy).
- **`eval.explain.explain_countermodel`** — any countermodel witness (Kripke
  model, Tarski structure, Z3 assignment, Verdict-layer dict) rendered as 2–6
  short deterministic English sentences. `api.countermodel` now uses it for
  `explanation_nl`: structured Kripke witnesses are rebuilt and narrated
  world by world (with the world-0 check evaluating the FOLDED goal
  `(∧ premises) → φ`), with the old one-line gloss as the fallback.
- **Structured Kripke witnesses**: every `"kripke"` countermodel dict from
  `modal-tableau` and `kripke-enum` now carries a JSON `"data"` payload next
  to `"repr"`, with the public converters `kripke_model_to_dict` /
  `kripke_model_from_dict` round-tripping worlds, relations, valuation,
  nominals and per-world domains.
- **`semantics.free_logic`: `policy="supervaluation"`** — truth-value gaps
  from empty terms resolved by quantifying over all precisifications
  (supertrue / superfalse / gap), so `P(e) ∨ ¬P(e)` comes out supertrue even
  where `P(e)` itself is a gap.
- **`dl.owl_manchester`** — `parse_manchester` / `to_manchester` /
  `parse_manchester_axiom` for the ALC fragment of Manchester OWL syntax,
  with explicit rejections outside it.
- **`atp.resolution`: redundancy elimination** — tautology deletion plus
  forward/backward subsumption (one-sided matching, indexed, with a
  documented pattern cap) inside `refute`; public signatures unchanged, the
  step counter's meaning ("kept clauses") documented.
- **CLI subcommands** — `python -m unicode_fol_kit check | equiv | prove |
  countermodel | repair | translate …` with `--json` envelopes; the legacy
  single-formula invocation is untouched.

Added — **the Tier-2 HETS binding (Docker-first)**: the kit can now drive a
real HETS (Heterogeneous Tool Set) server end-to-end — CASL export, REST
client, a thirteenth registered backend, and the server's comorphisms as
dynamic translation edges. Every wire-protocol fact below was verified live
against the official `spechub2/hets:latest` image (HETS 0.108.0).

- **`fol.casl_export` — kit AST → CASL** (`to_casl_spec`, `formula_to_casl`,
  both re-exported at top level). CASL is natively many-sorted, so kit MSFOL
  exports WITHOUT the single-sort collapse every TPTP route needs: sort
  inference runs a union-find over predicate/function/constant slots
  (bound sorted variables and `name:Sort` constants anchor concrete sorts,
  equality unifies its sides, unconstrained classes fall back to the default
  sort), and a class with two distinct concrete sorts, an arity conflict, a
  free variable, or a CASL-reserved-word identifier refuses loudly. Goals
  are emitted as `%implied` axioms — exactly what Hets turns into proof
  obligations. Everything outside FOL/MSFOL (modal, fuzzy, Count/Measure,
  second-order, …) raises `NotImplementedError` naming the node class.
- **`unicode_fol_kit.hets` — REST-over-Docker client subpackage.** The GPL
  boundary is structural (this MIT process and the GPL Haskell server share
  a TCP socket, nothing else; the in-process spechub Python binding is
  documented as considered-and-rejected: GHC-build-only, Linux-only, GPL in
  the process). `hets.docker`: `HetsContainer` lifecycle manager and
  `discover_hets_url` (`$UFK_HETS_URL` → `localhost:8000` → optional
  auto-start; anything else raises `BackendUnavailable` with the exact
  commands to fix it). `hets.client`: stdlib-urllib `HetsClient` for
  upload (`/folder` + `/uploadFile`), development-graph JSON (`/dg`),
  prover/translation listing, theory rendering/translation (`/theory`),
  `/prove` and `/consistency-check` with per-goal
  Proved/Disproved/Open results normalized into stable dicts. Documented
  image quirks: the bundled eprover and Vampire wrappers are broken (always
  Open); SPASS, darwin and darwin-non-fd work.
- **`atp.hets_backend.HetsBackend`** — registry name `"hets"`, the
  thirteenth backend: CASL export → upload → `POST /prove` → Verdict, with
  reasoner+comorphism provenance in `detail` (e.g. `reasoner=SPASS,
  translation=CASL2TPTP_FOF`). Mapping: Proved → PROVED, Disproved →
  REFUTED (darwin-non-fd's finite-model disproof), Open → UNKNOWN
  (`incomplete` — NEVER refuted, see the image quirks). NEVER in a default
  chain (container start is minutes-expensive, the Isabelle rule), and
  `decide()` never starts a container — it only discovers running servers.
  `check_consistency()` is the extra route over `/consistency-check`
  (deliberately a plain dict, not a Verdict: PROVED must keep meaning "goal
  follows", not "premises consistent"). The roadmap's acceptance criterion
  is a live test: one genuinely many-sorted problem proved end-to-end by
  two different Hets reasoners (SPASS via CASL2TPTP_FOF, darwin via
  CASL2SoftFOL), each verdict carrying its own provenance.
- **`hets.bridge.register_hets_comorphisms`** — every comorphism the server
  offers for CASL becomes a registered translation edge `hets:<Name>`
  (source label `"casl"`, term type: CASL spec TEXT — the registry's term
  type is per-source-logic, and the kit deliberately does not pretend to
  parse SoftFOL/DFG output back into ASTs). `api.translate(spec_text,
  "casl", "hets:CASL2SoftFOL")` returns the translated theory text as Hets
  renders it; the native registry stays the offline core.
- New serial live-test marker `hets_live` (same convention as
  `isabelle_live`; CI excludes both), 101 tests across
  `test_casl_export` / `test_hets_client` / `test_hets_backend` /
  `test_hets_bridge` (92 from the wave itself plus the review-fix
  regressions below; offline suites fully server-free via stubs).

Fixed — **15 adversarial-review findings on the HETS wave** (6-dimension
review, 2 refuters per finding; the CWA local-stratification dimension
survived with zero findings). Soundness: CASL export now checks PREDICATE
and SORT names (including `default_sort`) against CASL keywords and word
shape — a directly-constructed `Atom("axiom", ())` or a keyword sort
produced specs HETS 500s on (live-confirmed); 0-ary `Function` terms render
bare (`f`, not the invalid `f()`); `upload()` percent-encodes both path
segments (an unencoded `#` silently truncated the stored filename);
`http.client` exceptions (e.g. `InvalidURL`) now honour the client's
RuntimeError contract; the plain-text `nothing to prove` response is the
legitimate empty goal list, not a JSON error. Contracts/docs: `theory()`
documents that `node` is effectively mandatory (the "single-node default"
claim was live-false); port-already-allocated `docker run` failures get
their own actionable `BackendUnavailable`; empty `$UFK_HETS_URL` ≡ unset
(documented as deliberate); `HetsBackend` documents that `url=` pairs with
direct `decide()` calls while chains want `$UFK_HETS_URL`, that ANY
reasoner may report Disproved, and that `check_consistency` passes
`RuntimeError` through; `register_hets_comorphisms` refreshes COMPLETELY —
edges a re-registered server no longer offers are unregistered (new
`ComorphismRegistry.unregister`), never left as stale closures; the README
install section now names HETS/Docker and every extra.

Added — **E and Zipperposition backends** (`atp.eprover_backend`, one shared
SZS/TPTP runner): registry names `"eprover"` and `"zipperposition"`
(fourteenth and fifteenth backends), never in a default chain. Discovery per
backend: `$UFK_EPROVER_CMD`/`$UFK_ZIPPERPOSITION_CMD` (a `wsl:` prefix
forces the WSL route) → native PATH → the same binary inside WSL; a miss
raises `BackendUnavailable` with the per-platform acquisition paths (E:
`apt install eprover` on Ubuntu 24.04+/Debian — note 22.04 does NOT carry
it — or build from source; Zipperposition: opam only, no deb exists — where
absent the backend is honestly unavailable and its live tests skip). The
SZS status line is authoritative (the extractor now also accepts E's
`# SZS status …` hash-comment style — regression-tested), mapped through
the same ontology as Vampire; E is asked for `--proof-object` and a parsed
TSTP derivation lands in `Verdict.proof`, a Theorem WITHOUT a derivation
(Zipperposition's default output) keeps `proof=None` with the degradation
noted in `detail`, never silently. CI installs E on its Ubuntu 24.04
runner, so the E live tests run for real there.

Fixed — **26 adversarial-review findings on the post-HETS Tier-2 wave**
(8-dimension review, 2 refuters per finding, every fix regression-tested).
Soundness: the Twee goal check now requires an INJECTIVE variable binding
(a ground fact could previously "prove" its own universal generalisation
by collapsing distinct conclusion variables onto one Skolem term);
nanoCoP-M routes QUANTIFIED problems through the QML embedding for the
mandatory cross-check (the propositional tableau/enumerator are blind to
quantifiers — a K-frame proof soundly confirms any stronger logic, a
K-countermodel never alarms), maps quantifier variables through the
injective name map (kit `x1`/`X1` no longer silently unify as one Prolog
variable), and treats the wrapper's exit code as authoritative (a stale
result line in a timed-out run's buffer is discarded; a code/text mismatch
refuses); `product_update` REFUSES an action model that omits a relation
name the base model carries (an omitted agent previously came out with an
EMPTY product relation — vacuously omniscient, factivity broken — and the
old test pinning that behaviour is rewritten to the refusal contract);
`api.check(signature=Signature)` now also reports SORT violations
(`kind="sort_mismatch"`) instead of silently projecting them away;
`Signature.validate`/`from_formulas` descend into
Cardinality/SortedCardinality set-builder formulas (buried predicates were
invisible to declaredness/arity/sort checks and inference); the CI
eprover install step is Linux-gated (it crashed the Windows leg's pwsh).
Contracts: `TweeBackend.decide` returns ERROR verdicts instead of leaking
`RuntimeError` (broken WSL) or `ValueError` (a Theorem whose proof text
falls outside the distilled grammar — now honestly ERROR "refusing PROVED
without verification"); E/Zipperposition/nanoCoP discovery reads env
overrides FRESH on every call (a cached miss no longer freezes the
process); `Signature.merge` folds vacuous `arg_sorts=(None,…)` before
comparing (spurious conflicts gone); the MCP tools share ONE parse-error
shape (`{"ok": False, "argument": …, "errors": […]}` across every
argument position) and `translate` parses `"alc"` terms via the DL
grammar (the registered concept edges were unreachable through MCP);
`parse_sbn` validates accessibility before returning (a cross-NEGATION
offset can no longer hand out a silently invalid DRS). Docs: stale
Signature design note, ActionModel/`public_announcement_action`
docstrings, README install section (Twee, nanoCoP-M), the HETS-wave test
count, and the CI header comment all corrected to reality.

Added — **`unicode_fol_kit.drt` — Discourse Representation Theory**: the
one NL phenomenon single-sentence FOL structurally cannot express —
cross-sentence anaphora and donkey sentences — as a first-class subpackage.
`DRS` + the classical Kamp/Reyle condition core (`Pred`/`Eq`/`Neg`/`Impl`/
`Or`) with the textbook ACCESSIBILITY relation enforced by `validate()`
(antecedent referents accessible in the consequent, Neg/Or-internal ones
not); `parse_drs` for a compact box notation (`[x, y | Farmer(x),
Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]`) and `parse_sbn` for a
precisely bounded subset of the Parallel Meaning Bank's Sequence Box
Notation (sense lines → predicates, role/offset targets, TAB-scoped
NEGATION; every unsupported construct refused BY NAME);
`resolve_anaphora` binds explicit PRONOUN markers most-recent-first over
the accessibility layers (ambiguity raises under `strict=True`, is picked
and RECORDED otherwise); `drs_to_fol` is the standard translation whose
donkey rule (∀-quantified antecedent referents) is tested end-to-end:
the classic donkey sentence plus facts entails `Beats(john, daisy)`
through `api.prove` (z3), and every closed DRS exports a formula
`api.check` certifies closed. 66 hand-derived tests.

Added — **Twee with an independent proof checker**
(`atp.twee_entailment` / `atp.twee_check` / `atp.twee_backend`, registry
name `"twee"`, the seventeenth backend; never in a default chain). Twee
(nick8325, equational superposition) decides UNIT-EQUALITY problems and
prints human-readable rewrite-chain proofs — which this kit REFUSES to
take on faith: `twee_check.check_twee_proof` re-derives every rewrite step
by one-directional matching against the cited axiom/lemma (deliberately
NOT `unify`, which would unsoundly bind proof-term variables),
alpha-checks every restated axiom against the caller's real premises, and
verifies lemma order and chain endpoints; the backend runs the checker on
EVERY proof and reports ERROR instead of PROVED when verification fails.
Fragment honesty: only (∀-closed) equations are accepted — anything else
is UNKNOWN/`unsupported` before any subprocess runs. Documented from live
Twee 2.6.1 output (the `The conjecture is true!` banner, per-equation
canonical `X`/`Y`/`Z` variables, Skolemized goal variables, `tuple(...)`
conjunction goals whose slot order needs a bijection search — all found by
experiment, not assumed); the checker rejects all 8 hand-crafted tampered
proof variants in the suite (wrong axiom, flipped direction, skipped step,
forward lemma citation, …). Discovery `$UFK_TWEE_CMD` → PATH → WSL. 85
tests (79 offline on captured output, 6 live via the WSL binary).

Added — **Common knowledge + BMS action models**
(`semantics.action_models`): one-step `everybody_knows` (`E_G`) and
fixpoint `common_knowledge_holds` (`C_G` via the reflexive-transitive
closure of the union of the group's `K:` relations — the reading argued in
the docstring against FHMV's one-or-more-steps variant, equivalent on the
reflexive frames the kit's `Knows` assumes), `ActionModel` (events,
preconditions, per-agent event relations — purely epistemic: factual
postconditions are a documented non-goal), `product_update` (the
Baltag–Moss–Solecki product; worlds are literal `(w, e)` pairs), and
`public_announcement_action` whose product update is DIFFERENTIALLY tested
to agree exactly with the existing PAL `announce()`. Acceptance is the
roadmap's named criterion: the full Muddy Children scenario (3 children,
2 muddy; 8→7→4 worlds) hand-derived and run through BOTH routes, with the
classic round-2 knowledge result and the common-knowledge-after-public-
announcement check; plus the 2-event private announcement (anne learns φ,
bert cannot know that she did). 44 hand-derived tests.

Added — **nanoCoP-M as an opt-in, MANDATORILY cross-checked modal backend**
(`atp.nanocop_backend`, registry name `"nanocop"`, the sixteenth backend;
never in a default chain). nanoCoP-M (Jens Otten, GPL, Prolog) natively
decides FIRST-ORDER modal logic D/T/S4/S5 with explicit domain conditions —
power the kit accepts only under an asymmetric trust policy: a `Theorem`
answer is re-run through `modal-tableau` (definitive disagreement → ERROR
soundness alarm; agreement or inconclusive → PROVED with both provenances
in `detail`), and a `Non-Theorem` claim becomes REFUTED **only** when
`kripke-enum` independently finds a countermodel (attached as the
certificate) — otherwise it stays UNKNOWN/`incomplete` with the claim
recorded, because FO modal validity is undecidable and a proof-search
failure is not a refutation certificate. The translator emits the shipped
ReadMe's exact syntax (`f(...)`, `#`/`*` box/diamond, `,`/`;`, `all X:`)
with injective name mapping (collision → refusal, the NXF discipline), and
the wrapper script's own report line (`… is a modal (s4/cumul) Theorem`) is
parsed back: a caller-requested `logic=`/`domain=` that contradicts what
the user's `nanocopm.sh` is configured to run is an ERROR pointing at the
script, never an answer from the wrong logic. Discovery:
`$UFK_NANOCOP_CMD` (with `wsl:` prefix) → PATH → WSL; needs the user's own
nanoCoP-M + ECLiPSe/SWI-Prolog install, documented in the module.

Added — **`fol.signature` — a first-class Signature object** (`Signature`,
`PredicateDecl` / `FunctionDecl` / `ConstantDecl`; all frozen): the canonical
carrier for vocabulary declarations. `from_formulas` infers arities,
constant sorts and the sort set from ASTs (cross-formula arity conflicts,
constant-vs-function clashes and double-sorted constants refuse loudly);
`from_dict` accepts BOTH the loose `api.check` convention and a richer
explicit form, `to_dict` round-trips with stable ordering; `validate`
reports undeclared symbols, arity mismatches and concrete-sort mismatches;
`merge` unions with loud conflicts. `api.check(signature=…)` now also
accepts a `Signature` (projected onto the loose convention so the
did-you-mean diagnostics stay identical).

Added — **`eval.metric_hf` — the first NL→FOL metric for the HuggingFace
`evaluate` ecosystem** (a verified-empty niche). `compute_fol_metrics`
(pure Python, NO evaluate dependency) scores prediction/reference batches
per pair through `parse_any` + the graded `equivalent` ladder and
aggregates `{exact_match, equivalence_accuracy, mean_partial_credit,
parse_failure_rate, solver_unknown_rate, n}` — the honesty contract made
metric-shaped: a solver-level `None` counts neither as right nor wrong,
its mass is reported separately so users can compute bounds.
`FolEquivalence` (extra `[hf]`) wraps it as a real `evaluate.Metric`;
importing the module never needs the extra, only instantiating does.

Added — **`fol.dialect_detect`** — the dialect-detection order behind
`api.parse_any` extracted into one pure, importable source of truth:
`detect_dialects(text)` returns the ORDERED candidate list (smtlib →
annotated TPTP → LaTeX → bare TPTP/Prover9 on ASCII text → always
`"unicode"` last), `DIALECT_SIGNALS` documents each give-away regex, and
`parse_any` now consumes exactly this list (behavior unchanged,
regression-covered end-to-end).

Added — **`unicode_fol_kit.mcp` — the kit as an MCP server** (optional extra
`[mcp]`, MCP SDK >= 2.0; run with `python -m unicode_fol_kit.mcp`). Nine
tools projecting the seven-verb API faithfully — `parse_formula` (dialect
auto-detection, unicode rendering next to the JSON AST), `check_formula`,
`prove` / `find_countermodel` (full Verdict/countermodel dicts, structured
`{"error": {type, message}}` payloads for `BackendUnavailable`/`ValueError`
instead of tracebacks), `check_equivalence` (the graded tri-state ladder),
`diagnose` (ONE repair round: over MCP the client LLM *is* the fixer —
apply the suggestion, call again), `translate` (comorphism registry; the
text-typed `"casl"` source passes through verbatim for the `hets:<Name>`
edges), `verbalize`, and `list_backends` (registry + default-chain
introspection). Deliberately NOT imported by the package `__init__` — the
SDK stays optional; the subpackage raises a clear install hint when it is
missing. 16 tests, including two through the real MCP `list_tools` /
`call_tool` layer.

## [0.19.0] - 2026-08-10

Fixed — **two measured soundness gaps where a route reported plainly valid
principles as invalid**, both because a relation or a model class was left
unconstrained. Each is pinned by a regression test.

- **Modus ponens for `□→` was not valid; it is now, by default.**
  `semantics.conditional` quantified over *every* nested sphere system,
  including the **empty** one — under which `A □→ B` is vacuously true even
  where `A` holds at the evaluation world. So `cf_valid((P ∧ (P □→ Q)) → Q)`
  and `cf_valid((P □→ Q) → (P → Q))` both came back `False`, with the
  countermodel `spheres={w: []}` in each case, and `CounterfactualModel`'s
  docstring promised a centering ("`w` in the first") the code did not impose.
  The sphere class is now an explicit argument: `centering="none"` (Lewis
  **V**) / `"weak"` (**VW**, the new default) / `"strong"` (**VC**), listed in
  the new `CENTERING_LEVELS`. Under the default, modus ponens and weak
  centering are valid; strong centering `(P ∧ Q) → (P □→ Q)` still needs
  `"strong"`; and antecedent strengthening, contraposition and transitivity
  stay invalid at all three levels — the non-monotonicity is untouched.
  *(Behaviour change for callers who relied on the old verdicts: pass
  `centering="none"` to get Lewis V back. `cf_valid(φ, 3)` positional calls are
  unaffected — the new argument is keyword-only.)*
  The Isabelle route had the same gap (its only premise was `nested Sel`) and
  takes the same argument with the same default, so
  `isabelle_decide_counterfactual` and `cf_valid` decide the same logic.
  Excluding the empty sphere system also deleted the `|W| = 1` countermodel that
  a *nested* counterfactual relied on, so the **default world bound had to grow
  with it**: `max_worlds` now defaults to `DEFAULT_MAX_WORLDS[centering]` —
  3 at `"weak"` / `"strong"`, 2 at `"none"`. Two worlds is structurally too few
  at the centered levels, in two different ways. At VC `{w}` is pinned as the
  innermost sphere, so refuting a disjunction of two counterfactuals needs three
  worlds: Stalnaker's conditional excluded middle `(A □→ B) ∨ (A □→ ¬B)`, which
  VC leaves open, was reported **valid**. At VW the plain schemas are settled at
  two worlds but nested ones are not: importation
  `(A □→ (B □→ C)) → ((A ∧ B) □→ C)` was correctly invalid before centering
  and became **valid** after it. Both are `False` again at the new default, with
  verified three-world countermodels. `"none"` keeps the smaller bound because
  its enumeration is 26 sphere systems per world against VW's 11 (measured: a
  three-atom schema is seconds at VW, minutes at V) — so default verdicts at
  *different* levels are searched to different depths and are not directly
  comparable; pass an explicit `max_worlds` when comparing levels. No row of the
  ten-schema Lewis battery moves between the two bounds. At the centered levels
  the default bound now also matches `isabelle_decide_counterfactual`'s
  `card="1-3"`.
- **`fol.qml` asserted nothing at all about the temporal, one-step and deontic
  relations** — not even typing — while `hol.isabelle_modal` already emitted
  `t_refl` / `t_trans` / `n_in_t` / `t_in_nstar` / `d_serial`, so the two routes
  disagreed. `Ⓞφ → Ⓟφ`, `Ⓖφ → φ`, `Ⓖφ → ⒼⒼφ`, `Ⓖφ → Ⓕφ` and `Ⓖφ → Ⓝφ` were all
  reported invalid. `qml_axioms` now emits typing plus the frame conditions
  (`T` reflexive + transitive, `N ⊆ T`, `D` serial) for the relations the
  formula actually uses, on by default and gated on `formula=` — for a
  `□`-only formula the emitted list is member-for-member identical to before
  (7 axioms), while the ungated "whole background theory" call now returns 15
  instead of 7 (17 instead of 9 for `frame="S4", mode="increasing"`).
  `Ⓝφ → φ`, `Ⓕφ → Ⓖφ`, `Ⓞφ → φ` and `φ → Ⓞφ` correctly stay invalid. A deontic
  `True` now means "valid over every **serial-deontic** model". A first-order
  theory cannot pin down a transitive closure, but a first-order *consequence*
  of `T = N*` can be stated, and `qml_axioms` emits it whenever `T` and `N` both
  occur (`first_step`: `T(w,v) → w = v ∨ ∃u (N(w,u) ∧ T(u,v))`, the FO shadow of
  the HOL routes' `t_in_nstar`, gated exactly like `n_in_t` and off under
  `temporal_closure=False`). It holds in every `T = N*` model — checked against
  the canonical expansion of every one-step relation on ≤ 3 worlds and 4000
  random ones on 4 — so it over-validates nothing, and with it the fixpoint
  unfolding `(φ ∧ ⓃⒼφ) → Ⓖφ` is provable here. Only temporal induction
  `(φ ∧ Ⓖ(φ → Ⓝφ)) → Ⓖφ` stays out of reach, and is documented as pointing at
  `isabelle_decide_modal`. *(Behaviour change: temporal and deontic formulas
  previously reported invalid are now valid. `temporal_closure=False` restores
  the weaker temporal reading, for parity with the exporters' own flag.)*
  Not fixed in this release, and now **documented** in the quantified-modal
  guide instead: `resolution.prove` lowers purely propositional modal input with
  `standard_translation`, which still asserts nothing about `T`/`N`/`D`, so
  `resolution.prove([], Ⓖ P → P)` stays `False` where `qml_is_valid` is `True`
  (a resolution `False` never claims invalidity, so this is a coverage gap, not
  an unsoundness).

Added — **cross-family bridge axioms**, opt-in on every route that can express
them. `frame=` and `systems=` each constrain one relation; a bridge relates
**two** relations of different families, which is what these principles need:
`knowledge_implies_belief` (`K_a φ → B_a φ`, condition `Rb ⊆ Rk` / fact
`rb_in_rk`), `sincerity` (`Say_a φ → B_a φ`, `Rb ⊆ Rs` / `rb_in_rs`) and
`ought_implies_can` (`Ⓞ φ → ◇φ`, `∀w ∃v (D(w,v) ∧ R(w,v))` / `d_meets_r`).

- Available as `bridges=` on `qml_axioms` / `qml_is_valid` / `qml_equivalent`
  (registry `fol.QML_BRIDGES`, also re-exported at the top level) and on
  `isabelle_modal_theory` / `to_isabelle_modal` / `modal_axiom_names` /
  `to_thf_modal_full` / `thf_full_frame_axioms` / `isabelle_decide_modal`
  (registry `hol.BRIDGES`, single-sourced between the Isabelle and THF
  emitters so the fact names cannot drift). Nothing is on by default; an
  unknown name raises `ValueError` listing the known ones.
- Every route emits the **exact** correspondent of each schema, verified by a
  brute-force sweep over all frames on ≤ 2 worlds, so **one option name denotes
  one logic everywhere**. `ought_implies_can` is deliberately not the folklore
  `d ⊆ r`, which measurably fails to validate `Ⓞφ → ◇φ` on its own and, with
  seriality, over-validates both `□φ → Ⓞφ` ("whatever is necessary is
  obligatory") and `Ⓟφ → ◇φ`. `fol.qml` shipped the inclusion in an earlier
  draft of this release and now emits the same meet condition as the HOL routes;
  the frame `W = {0,1,2}`, `D = {(0,1),(0,2),(1,1),(2,2)}`,
  `R = {(0,1),(1,1),(2,2)}` satisfies the meet condition and refutes both
  artefacts, and `test_hol_bridges.py` pins the agreement in both registries.
- Requesting a bridge whose partner family does not occur in the formula raises
  `ValueError` on **every** route rather than skipping it (a weaker logic than
  requested) or emitting it anyway (`d_meets_r` entails seriality of the alethic
  `r`, which would quietly make `□P → ◇P` valid under `frame="K"`).
  `qml_axioms()` without `formula=` is the whole-background-theory call, in
  which every relation is in scope, so nothing is rejected there. The native
  modal tableau refuses `bridges=` outright with a `NotImplementedError` naming
  the routes that can honour it: every one of its structural rules acts inside a
  single relation.

Changed — **the runner now forwards the full logic selection to every theory it
builds.** `isabelle_decide_counterfactual` gained `centering=` (default
`"weak"`, matching the emitter and `cf_valid`) and `isabelle_decide_modal`
gained `bridges=`. Each reaches *all* emission sites — the prove theory, the
proof battery's `unfolding` / `using` lists, and the nitpick theory. That is
load-bearing, not tidiness: the two steps decide opposite questions, so an
option reaching only the prove step degrades to `UNKNOWN`, while one reaching
only the refute step lets nitpick certify a "genuine" counter-model outside the
requested class — a false `INVALID`. An unknown `centering` level is reported as
a `ValueError` *before* the install lookup, so a typo is a typo even on a
machine with no Isabelle. Under `bridges=`, the reconstructed Kripke witness on
an `INVALID` verdict is skipped, since the toolkit's evaluator has no notion of
a cross-family frame condition; the verdict itself is unaffected.

## [0.18.0] - 2026-07-28

Added — two checker-side capabilities for certifying external provers (built for,
but not limited to, the FitchAsATP calculus-comparison engine):

- **Independent resolution-proof checker** (`atp.resolution_check`):
  `ResolutionStep` / `ResolutionDerivation` / `ResolutionCheckResult`,
  `verify_resolution_proof` (step-level errors, `refuted` flag),
  `check_resolution_proof`, `render_resolution_proof` (□ for the empty clause).
  A derivation lists clauses justified as `input` / `resolve` / `factor`; the
  checker re-derives each step's licence itself. Deliberately shares **no
  inference code** with any searcher: unification (Robinson, occurs check) is
  reimplemented in-module and differential-tested against `fol.unification`,
  and clause comparison is an **exact** alpha-equivalence backtracking search
  (variable bijection + literal bijection), not a canonical-form shortcut —
  `{P(x,y), P(y,x)}` matches `{P(u,v), P(v,u)}`, `{P(x,x)}` never matches
  `{P(x,y)}`. Hand-checked battery includes the classic soundness traps:
  simultaneous double-cut to □ is rejected, Robinson's factoring-required
  refutation verifies, over-general resolvents and instance-as-input restates
  are rejected.
- **TPTP header metadata** (`parse_tptp_problem` / `load_tptp_problem`,
  `TptpProblem`, `TptpHeader`): the standardized `%` header block (`File`,
  `Domain`, `Problem`, `Status`, `Rating`) is recovered by a raw-text line
  scan that runs independently of the Lark grammar — `Status` (ground-truth
  verdict) as its first token, `Rating` as the first float (`?` → `None`),
  every raw `%` line preserved verbatim in `comments`. The existing
  `parse_tptp` / `load_tptp` / `TptpFormula` API is byte-for-byte unchanged
  and regression-pinned.

## [0.17.0] - 2026-07-21

Added — **every logic in the kit now has an automated proof-theory route, and
every remaining Isabelle-export gap is closed.** Nine capabilities, each with
hand-checked tests and a differential battery against an existing oracle:

- **Intuitionistic proof search** (`int_prove` / `int_decide`,
  `atp.lj`): Dyckhoff's contraction-free **G4ip** calculus — a genuine,
  terminating decision procedure for propositional intuitionistic logic. The
  kit previously had only a proof *checker* plus the bounded Kripke search.
  Verified against 34 hand-checked textbook facts, the S4/GMT oracle and 250
  seeded random formulas. This also **fixes `int_valid`'s soundness gap at the
  root**: for propositional input the positive verdict now comes from G4ip, so
  `int_valid((p→q)∨(q→r)∨(r→p))` is correctly `False` at DEFAULT arguments
  (its smallest countermodel needs 4 worlds; the old 3-world default said
  "valid"). First-order input keeps the honest bounded contract.
- **Relevant logic B, Isabelle-certified** (`hol.isabelle_relevant` +
  `isabelle_decide_relevant`): a Routley–Meyer shallow embedding following
  `isabelle_conditional`'s premise-not-axiomatization design, so nitpick can
  certify countermodels as *genuine*; `rel_valid`'s bounded `True` finally has
  a certified positive counterpart (9/10 hand-checked B-facts certified live
  end-to-end during development).
- **ILL and Lambek derivations exported to Isabelle**
  (`hol.isabelle_substructural`): the sequent rules become an
  `inductive derivable` predicate (multiset antecedent for ILL,
  *list* antecedent for Lambek — order is the point), and the concrete
  Python-found derivation is replayed as a machine-checked lemma
  (`to_isabelle_ill` / `to_isabelle_lambek` + `*_derivation_theory`).
  Plus the ILL **additive units ⊤ and 𝟘** (nodes, parser glyphs, ⊤R/0L rules
  in search and checker).
- **Public announcement logic (PAL)** — `[φ!]ψ` / `⟨φ!⟩ψ` are now real,
  parseable operators (`Announce` / `AnnounceDiamond`, modal mode) with the
  full node contract (round-trip printing incl. LaTeX, serialisation).
  `reduce_announcements` implements the standard reduction axioms by syntactic
  relativization, so the modal tableau **decides** PAL (the reduction axiom
  `[φ!]K_aψ ↔ (φ → K_a[φ!]ψ)` is valid, the famous `[φ!]K_aψ → K_a[φ!]ψ` is
  not); `satisfies_modal` evaluates announcements directly via the restricted
  model — the oracle a 100-formula random differential pins the reduction
  against. Temporal operators under an announcement are rejected with the
  reason (restriction of a closure ≠ closure of the restriction).
- **Arbitrary finite truth-matrix export** (`to_thf_matrix` /
  `to_isabelle_matrix` + entailment variants): the K3/LP reification is now
  data-driven over ANY `TruthMatrix` — including Belnap–Dunn **FDE** and
  user-built matrices; the K3/LP exporters delegate to it.
- **ALC ↔ the rest of the kit** (`dl.translate`, `dl.parser`): the standard
  translation `concept_to_fol` (multi-role, capture-avoiding) plus
  TBox/ABox/GCI forms and single-role `concept_to_modal`, differentially
  validated against the ALC tableau on 80 concepts — so ALC reasoning can
  reuse the FOL provers and Isabelle/THF exports. And ALC concepts finally
  **parse from strings** (`parse_concept` / `parse_gci`, the `⊤ ⊥ ¬ ⊓ ⊔
  ∃r.C ∀r.C ⊑` glyph syntax the renderer emits, round-trip-pinned).
- **Free-logic decision procedures** (`free_is_valid`, `free_countermodel`,
  `free_find_model`, `free_entails`): bounded exhaustive search over
  inner/outer-domain splits and partial denotation, with the same honest
  contract as `rel_valid`/`cf_valid` (False = verified countermodel).
- **Dependence logic → ESO** (`dependence_to_eso`): the Skolem-function
  translation for the guarded/slashed sentence fragment, emitting a
  `SecondOrderQuantifier` formula ready for `satisfies_so` /
  `hol.secondorder`; faithfulness pinned by exhaustive structure-enumeration
  differentials against `team_models` (which caught and fixed a real
  slashed-∃ scoping subtlety during development). And **circumscription → SO**
  (`circumscription_formula` / `circumscription_entails_so`): McCarthy's
  second-order axiom as a Node, differentially validated against
  `minimal_entails`.
- **Parser/LaTeX surface completeness**: all 11 broken LaTeX round-trips fixed
  (incl. the two SILENT mis-parses — `\mathsf{i}` nominals and `\mu` measures)
  with a registry-driven 41-operator round-trip battery;
  `parse_latex` gained `dependence`/`linear`/`lambek` modes; the CLI's
  `--mode` now accepts `modal` / `second_order` / `dependence` / `linear` /
  `lambek`; and single-letter function names (`f(x)`) now parse as functions
  in term position (previously they crashed the re-parse of the kit's own
  output).

Fixed — **five soundness/faithfulness bugs found by the proof-theory
completeness sweep** (each with a pinned regression test):

- **Łukasiewicz formulas no longer collapse silently to classical logic.**
  `is_valid` / `is_valid_resolution` on a fuzzy-parsed formula quietly applied
  the classical reduction and returned verdicts for the WRONG logic —
  `is_valid(MSFLParser(fuzzy=True).parse("P ∨ ¬P"))` came back `True` while
  `fuzzy_is_valid` correctly says `False` (weak min/max disjunction has no
  excluded middle). The Łukasiewicz nodes now refuse `to_z3` / `to_prover9` /
  `to_tptp`, and the normal forms (and the resolution prover on top of them)
  refuse fuzzy input, each pointing at `fuzzy_is_valid` /
  `semantics.fuzzy.evaluate`; the collapse itself remains available as the
  explicit, documented opt-in `to_fol(node)`. *(Breaking for callers who relied
  on the silent collapse: insert `to_fol(...)` to keep the old reading.)*
- **`to_thf_modal_full` conflated distinct nominals that sanitise alike.**
  `@A P ∧ @a Q` emitted ONE world constant `nom_a` for both nominals — a
  loadable file that meant a different formula. Nominal names are now resolved
  through a per-formula deduplicating map (`nom_a` / `nom_a_2`), and a user
  constant literally named `nom_i` can no longer capture a nominal's world.
- **Reserved-name collisions in the THF/Isabelle exporters.** A user predicate
  named like a built-in functor (`r`, `t`, `mbox`, `muntil`, `says`, `rs`, …)
  silently re-declared the built-in at a conflicting type (THF) or emitted
  duplicate `consts`/`abbreviation` names Isabelle rejects. Both exporters'
  name resolvers now pre-claim their full built-in vocabulary
  (`SymbolNames(reserved=…)`), pushing user symbols to suffixed variants; the
  `isabelle_modal` reserved set gained the identifiers introduced with the
  Says/Wants/past-temporal/Until/Since support.
- **The qml embedding left constants untyped.** In the World/Object-guarded
  first-order embedding nothing forced a constant into `Object`, so
  `qml_is_valid(∀x P(x) → P(c))` was spuriously `False` — and an
  Object-guarded agent frame axiom (`systems=`) could never fire for a *named*
  agent (`K_alice P → P` stayed invalid under `{"epistemic": "T"}`).
  `_validity_formula` now emits Object-typing facts for every constant, number
  and function of the formula (functions map objects to objects).
- **The resolution prover's verdicts were hash-seed-dependent.** Saturation
  iterated Python sets, so clause processing order — and hence whether a goal
  closed within `max_steps` — varied between runs of the same call. The loop
  now orders everything by clause content (variables renamed in sorted order,
  literals visited by surface form, seed clauses smallest-first). Reproducible,
  and dramatically faster on quantified-modal images: the Barcan formula now
  closes in ~1 000 steps instead of ~200 000.
- Also fixed: `cf_satisfies` / `cf_valid` silently accepted first-order atoms
  (`P(x) □→ P(x)` returned a definite verdict for an out-of-contract formula,
  where `to_isabelle_conditional` rejects the identical input); they now raise
  the same propositional/ground contract error. And `thf_modal`'s docstrings
  still claimed "`Until` is omitted (raises)" — stale since the impredicative
  `muntil`/`msince` fixpoints landed; corrected.

Added — **the assertive/bouletic family in every first-order route, and
first-order modal input in the resolution prover**:

- `standard_translation` translates `Say_a` / `Want_a` as per-agent box
  relations `Rs_a` / `Rw_a` (mirroring `Rk_a`/`Rb_a`), so `resolution.prove`
  decides the propositional Say/Want fragment (the K axiom for `Say_a` was the
  inventory's crash repro). `qml` gained agent-indexed `Rs`/`Rw` branches plus
  `assertive`/`bouletic` entries for `systems=` — `Say_a P → P` is decidable
  as factive-on-demand across qml, the THF export and the Isabelle export.
- `resolution.prove` no longer raises the stale "future work" error on
  quantified modal input: it lowers the folded consequence through the qml
  first-order embedding (constant domains, frame K — `qml_is_valid`'s
  defaults) and saturates the image, with the step budget scaled to the larger
  translation. Both Barcan directions are provable; `False` still means "not
  proved within the bound".
- `isabelle_modal_theory` / `to_isabelle_modal` / `isabelle_decide_modal`
  gained the `systems=` parameter `to_thf_modal_full` already had (per-agent
  frame axioms for `rk`/`rb`/`rs`/`rw`, the agent schematic). Systems whose
  conditions have no per-agent schema (GL's Löb, S4.2/S4.3) are rejected
  loudly in BOTH exporters instead of being silently weakened.
- `to_thf_modal_full` gained `temporal_closure=` for parity with the Isabelle
  emitter (opt out of `t_refl`/`t_trans`, keeping the `tnext ⊆ t` link).

Changed — **every generic proof-theory entry point now answers or points,
across ALL of the kit's logics.** The classical tableau, Fitch search,
resolution/normal forms and the modal tableau reject substructural
(ILL/Lambek), team-semantic (dependence/IF), second-order and Łukasiewicz
input with one clean `NotImplementedError` naming the right decision procedure
(`ill_prove` / `lambek_prove` / `team_satisfies` / SO sequent rules /
`fuzzy_is_valid`) — previously these surfaced as bare `ValueError: no rule for
Tensor` from inside the rule dispatcher, an unhinted `TypeError` from `to_nnf`,
or (worst) a silent `False` from the Fitch search on the genuine ILL theorem
`A ⊸ A`. `modal_tableau` explains the GL frame's converse-well-foundedness
instead of listing it as an unknown name, the deep-embedding fallback points at
the full-family Isabelle/THF exporters, and `qml.to_thf_modal` points at
`to_thf_modal_full`.

Added — **the counterfactual conditionals `□→` and `◇→` are now parseable
operators.** Lewis's "would" and "might" conditionals existed only as the API
functions `would(model, world, antecedent, consequent)` / `might(…)`; they now also
parse in **modal mode** (`MSFLParser(modal=True)`) as the new `Would` / `Might`
nodes, so a counterfactual can be written as a formula string, rendered, serialised
and round-tripped like any other connective.

- **Why modal mode rather than a mode of its own:** indicative modals and
  subjunctive conditionals co-occur in ordinary prose, so a sentence mixing `◇`
  and `□→` must parse as a single formula; a standalone mode could not express it.
- **Precedence** is the `Ⓤ` / `⒮` level: tighter than `→` and `↔`, looser than `∧`
  and `∨`, so `A ∧ B □→ C` groups as `(A ∧ B) □→ C`. The glyphs *begin with* `□`
  and `◇`, so their terminals carry explicit priority — without it `A □→ B` would
  lex as a box followed by a material arrow and silently parse as a modalised
  material conditional, precisely the confusion the connective exists to avoid.
- **`cf_satisfies(formula, model, world)`** evaluates a whole parsed formula against
  a `CounterfactualModel`, and counterfactuals may now **nest** (`A □→ (C □→ A)`) —
  not expressible through the argument-passing form, which took propositional
  antecedents and consequents. `would` / `might` keep their signatures and share the
  one sphere condition, so the two entry points cannot drift apart.
- **Two boundaries are enforced, not guessed.** There is no first-order export
  (`to_z3` / `to_prover9` / `to_tptp` raise): collapsing `□→` to the material `→` is
  the mistake the connective exists to avoid. And a similarity ordering is not an
  accessibility relation, so `satisfies_modal` rejects a counterfactual, `cf_satisfies`
  rejects `□`/`◇`, and the modal and classical tableaux raise rather than return a
  validity verdict they have no sphere rule to justify.

`to_english` marks the subjunctive ("if A were the case, B would be"), keeping the
counterfactual distinct from the material reading in the verbalization too.

Added — **Isabelle/HOL export and decision for the counterfactuals:
`hol.isabelle_conditional` + `isabelle_decide_counterfactual`.** The modal exporter
embeds `□`/`◇` over an accessibility relation, which is the wrong structure for a
counterfactual, so the sphere semantics gets its own shallow embedding: a formula
becomes a predicate on worlds, the sphere system is the uninterpreted constant
`Sel`, and validity is `nested Sel ⟹ ∀x. φ x`. The `CondC` clause is the same
truth condition `cf_satisfies` evaluates and the same as `CondM` in the verified
`deepshallow.conditional` faithfulness theory, so what Isabelle certifies is what
the toolkit computes. `◇→` is emitted as the dual `¬(A □→ ¬B)` rather than given a
constant of its own, so the theory cannot drift from the evaluator's derivation.

`isabelle_decide_counterfactual(φ)` follows the `isabelle_decide_fol` scheme:
proof battery ⇒ VALID, else `nitpick[expect = genuine]` over the world type ⇒
INVALID, else UNKNOWN. Two empirically-forced design points, both pinned by tests:

- **Nesting is a premise of the goal, not an `axiomatization`.** nitpick cannot
  certify a counter-model as *genuine* while axiomatised constants are in play (it
  downgrades to `quasi_genuine`, losing the refutation half of the procedure); as a
  premise, nitpick constructs the sphere system itself.
- **The proof battery is verit-first.** The `|` combinator has no per-method
  timeout and `blast` does not terminate on agglomeration
  `(A □→ B) ∧ (A □→ C) → (A □→ (B ∧ C))` — the validity whose proof actually uses
  the nesting premise — so a blast-first battery hangs before reaching verit
  (measured: 97 s and fails vs. ~9 s).

Isabelle-gated live tests certify the headline Lewis facts (identity,
agglomeration, weakened consequent, the would/might duality VALID; antecedent
strengthening and contraposition INVALID) and check the INVALID verdicts
differentially against a brute-force sweep of small sphere models through
`cf_satisfies`.

### Completeness: every entry point answers or points, never crashes

An exhaustive, empirically-verified inventory of every "unsupported node type"
raise across the exporters and internal provers, then closed: each gap either
**works now** (verified against an oracle) or raises **one clean error naming
the right tool**. `tests/test_completeness.py` pins every closed gap with the
inventory's exact repro.

**Isabelle/THF export — the full modal family emits.**

- `to_isabelle_modal` / `isabelle_modal_theory` now embed `Historically` (⒣) /
  `Once` (⒫) as box/diamond over the **converse** of the henceforth `t` (whose
  refl+trans axioms constrain the past readings identically — the converse of a
  refl+trans relation is refl+trans), `Previous` (⒴) as box over the converse of
  the one-step `n`, `Says`/`Wants` as agent-indexed K-boxes over `rs`/`rw` (no
  frame axioms — non-factive, non-veridical), and the hybrid `Nominal`/`@` via
  world constants `nom_<name> :: i` (the standard translation's reserved prefix).
- **Soundness fix found by the live differential:** the embedding's entity type
  was the *polymorphic* `'a`, and Isabelle gives every occurrence of a
  polymorphic constant its own type instance — so the two `says a` in
  `Say_a(P→Q) → (Say_a P → Say_a Q)` denoted two INDEPENDENT relation instances
  and nitpick "genuinely" refuted the valid agent-K axiom (a certified-looking
  **false INVALID**; `Knows`/`Believes` were equally affected). The embedding now
  declares one monomorphic `typedecl e`. A 10-fact live battery (valid ⇒ kernel
  proof, invalid ⇒ genuine countermodel) certifies the completed operators.
- The runner's refute step now defines `t = rtranclp n` whenever the closure
  relation is in use at all (previously only when `Next` co-occurred), so
  nitpick can construct the closure and genuinely refute non-theorems of the
  pure closure fragment — `⒫P → P` is now `INVALID` instead of `unknown`.
- `to_thf_modal_full` gains the same seven operators, plus `Until`/`Since` as
  **impredicative Knaster–Tarski least fixpoints** over `tnext` (TH0 quantifies
  over predicates, so the fixpoint Isabelle's `inductive` compiles to is
  directly shallow-embeddable — the previous rejection's "not (higher-order)
  shallow-embeddable" claim was factually wrong and is corrected).
- `to_thf_fol` / `to_isabelle_fol` accept `Count` (distinct-witnesses
  expansion), `Measure` (the uninterpreted `measure/2` the other exports emit),
  and `Contrast`; the msfol variants inherit them through `to_fol`.
- `to_isabelle_so` embeds `Cardinality` / `SortedCardinality` as HOL's native
  `card {v. φ}` (sort-guarded for the sorted variant); comparisons with a
  cardinality operand are numeric over `nat`, mirroring the Tarskian rule, and
  a category-error operand raises with an explanation. `to_thf_so` keeps
  rejecting (TH0 has no finite-set theory) but points at `to_isabelle_so`.
- `qml_translate` rejects `Since` with the same explanatory pointer `Until`
  already had (msince / the HOL embeddings), instead of the generic error.

**Internal provers — answers instead of raises.**

- `to_fol` now honours its own "classical FOL constructs only" contract:
  `Contrast` collapses to `∧` and `Count` expands via distinct witnesses (a
  relativized `SortedCount` keeps its sort guard inside the witness matrix).
  This fixes `to_nnf`/`to_cnf`/`skolemize`/resolution in one place.
- The classical tableau handles `Contrast` and `Count` directly, and — a
  pre-existing completeness gap — now seeds its γ-instantiation pool with the
  input's **free variables** read as constants (the universal-closure validity
  convention Z3 and resolution already used), so `¬∃x P(x) → ¬P(a)` proves
  instead of silently returning False. The three classical engines now agree on
  a shared battery.
- `unify` / `apply_subst` / resolution's standardize-apart handle `Measure`
  terms (slot-wise, purely syntactic — a `Measure` never unifies with a
  `Function` named "measure"; that spelling is an export convention).
- **Resolution decides the propositional-modal fragment**: modal input is
  folded into one local-consequence implication and lowered by
  `standard_translation` — sound + complete for K for free, cross-checked
  against the modal tableau. `fitch_prove` / `is_valid_fitch` route modal input
  to the modal tableau (previously the valid `□(P→Q), □P ⊢ □Q` silently
  returned **False** — a wrong answer, the worst failure mode of the lot);
  `find_fitch_proof` refuses modal input with a pointer, since it cannot
  fabricate a Fitch proof object.
- The modal tableau leaves temporal-closure operators **inert** instead of
  raising: branch closure stays sound (monotone), open models reach callers
  only after `satisfies_modal` verification, so `modal_decide` finally honours
  its documented valid/invalid/unknown contract — `ⒼP` is now a verified
  "invalid" with a countermodel, `ⒼP → P` an honest "unknown", and nothing
  crashes. Quantified constructs under a modal operator are treated as opaque
  literals under the same verified-or-unknown regime.
- `cf_valid` / `cf_countermodel`: a **bounded exhaustive sphere-model search**
  (the `rel_valid` contract: False is definitive and verified, True is
  no-countermodel-within-bound) gives the counterfactuals an in-process
  decision path that agrees with all six Isabelle-certified Lewis facts.
- The residual, genuinely-impossible cases (`Cardinality` in first-order
  provers, `SecondOrderQuantifier` in resolution, `□→`/`◇→` anywhere
  accessibility-relational) keep raising — but every message now names its
  reason and the right alternative tool.

**Developer loop.** The ~115 Isabelle-live tests carry a registered
`isabelle_live` marker; `pytest -n auto -m "not isabelle_live"` runs the other
~3100 tests in **~45 s** (previously the full serial suite took ~17 min).
CI/pre-release keep the live coverage via `-m isabelle_live`.

## [0.16.0] - 2026-07-14

Added — **CCG-style derivation trees with lambda-semantics (`CCGDerivation`).** A new
`unicode_fol_kit.fol.derivation` module builds and renders combinatory categorial
grammar derivations in the ccg2lambda / depccg idiom: a bottom-up composition tree
whose nodes carry a surface word, a CCG category, a combinator rule (`fa` / `ba` /
`bx` / `conj` / `lex` / `rp` / …), and the **lambda-term semantics** at that node.

- The semantics is genuinely *composed*, not written by hand: `CCGDerivation.forward`
  (`fa`) and `CCGDerivation.backward` (`ba`) apply one child's term to the other and
  reduce it with the toolkit's own `beta_reduce` (or `beta_eta_normalize` with
  `eta=True`), so a node's `term` is the real beta-normal form — checked in the tests
  against the parsed target formula. `leaf` / `unary` / `combine` build the rest.
- Three renderers mirror the `to_unicode_str` / `to_latex` / `tree_str` split:
  `to_text()` draws a Unicode "prooftree" (premises over an inference bar with the
  combinator at its right, then the category over the lambda-term) — a genuinely new
  rendering style for the toolkit (neither the indented `render_sequent_proof` nor the
  Fitch-bar `render_fitch` draws a Gentzen bar); `to_latex()` emits a `bussproofs`
  proof tree; `to_html()` returns a self-contained, theme-aware HTML page in the
  ccg2lambda idiom (category red, lambda-term blue, combinator at the bar).
- `reduction_derivation(term)` turns a beta-reduction path (`reduce_trace`) into a
  `CCGDerivation` chain, so a plain lambda reduction can be drawn with the same
  renderers.

New public names `CCGDerivation` and `reduction_derivation` (top level and
`unicode_fol_kit.fol`); a new guide page `docs/guide/derivations.md`. CCG *parsing*
(word → category → derivation) is out of scope — you supply the categories and
combinator structure; the toolkit composes and renders the semantics.

Added — **Tarskian evaluation of the counting, cardinality, and measure nodes.** The
two-valued evaluator previously raised `unsupported node type Count`; it now decides
`Count` / `SortedCount` (∃≥n / ∃≤n / ∃=n) and evaluates `Cardinality` /
`SortedCardinality` (`|{v : φ}|`) and `Measure` (`μ(e, d)`) as terms. A sorted binder
ranges over its sort's universe. `Measure` reads the binary function `measure`, the
same symbol `Measure.to_z3` and `Measure.to_prover9` emit, so a structure found here
interprets what the provers see. This makes the finite model finder work on counting
formulas end to end (`find_model`, `find_countermodel`).

**An order comparison `<` `>` `≤` `≥` now has three readings, in precedence order.**
Previously it had one — the extension lookup — which made every comparison over a
computed number silently `False`.

1. A **cardinality operand forces the numeric reading**: `|{v : φ}| > |{v : ψ}|`
   compares the counts. A cardinality is a natural number the evaluator computes
   itself, so no structure may reinterpret it; a declared extension does not override
   this, and a cardinality compared against a non-number raises instead of quietly
   answering `False`.
2. Otherwise a **declared extension wins**. The order symbols are ordinary relation
   symbols and a structure may interpret `<` over its domain however it likes — the
   reading `to_z3` / `to_prover9` assume, where the comparison is uninterpreted.
   Declared-but-*empty* still means the empty relation, so the model finder (which
   declares every scanned predicate and enumerates the empty extension among the
   candidates) is unaffected.
3. Otherwise, if **both operands evaluate to numbers**, arithmetic applies. This is
   what makes a `Measure` threshold work: `μ` is an uninterpreted function, so a
   structure may map it to numbers without also axiomatising `≥` over them, and
   `μ(x, temperament) ≥ μ(y, temperament)` no longer requires the user to spell out
   an order extension by hand. `bool` is deliberately not a number here — `True ≥
   False` must not quietly succeed as `1 ≥ 0`.

Anything else remains the empty relation, hence `False`; an absent extension is not
an error. The asymmetry between (1) and (2) is deliberate rather than an
inconsistency: a cardinality *is* a number, whereas a measure's values are whatever
the structure says they are.

Fixed — **variable binders beyond ∀/∃ were walked structurally** by three peripheral
passes, which recognised only `Quantifier` / `SortedQuantifier` as binders. `Count`,
`Cardinality`, their sorted variants, and the IF-logic `SlashedExists` all bind a
variable over a matrix, so the passes violated shadowing and captured free variables.

- **Soundness (`atp/fitch.py`).** ∀E computed a capturing instance, so the checker
  accepted `∀x ∃=2 y R(x, y) ⊢ ∃=2 y R(y, y)` — invalid, as the domain `{0, 1, 2}`
  with `R(x, y) ⟺ y ≠ x` refutes it. Substituting into a re-binding `∃=n x` also
  rewrote the binder slot itself, producing a malformed `∃=2 a Q(a)`.
- **`atp/sequent.py`.** Second-order comprehension instantiation captured a free
  object variable of the comprehension. Slash names are plain strings that
  `free_variables` cannot see, so a freshly minted binder name could silently collide
  with one and rewire the independence set; they are now avoided explicitly.
- **`semantics/modelfinder.py`.** A binder's bound variable was reported as free (and
  vacuously quantified by the universal closure), while a `SlashedExists` slash name —
  which *is* free — was missed. A `Count`'s bound `n` was registered as a domain
  constant, so a found structure carried a phantom constant and the enumerated space
  grew by a factor of the domain size, which can push a size past `max_candidates` and
  yield a spurious "no model". Sorted counting and cardinality binders never
  registered their sort, so no universe was enumerated for it.

The slash-set rewriting that `fol/_msfl_nodes.py` already specified is now the shared
`subst_slash_set`, so the prover copies cannot drift from it.

## [0.15.0] - 2026-07-11

Added — **non-ASCII (Greek) constant names.** A ground constant may now be written
with a Greek letter — e.g. a threshold `θ` in `μ(x, volume) > θ` (“too much”) — so a
bare `θ` lexes as a `CONSTANT` rather than being rejected. The reserved operator
glyphs **λ** (Lambda) and **μ** (Measure) are excluded and keep their operator
meaning. Scope is deliberately narrow: **constants only** — predicates, function
names, and variables stay ASCII.

The Kripke evaluator and the Z3 backend carry the raw unicode name directly. The
text-based, ASCII-only first-order back-ends (`to_prover9` / `to_tptp`) transliterate
it deterministically and reversibly via the new `constant_name_to_ascii` /
`constant_name_from_ascii` helpers: each Greek letter maps to its conventional name
(`θ` → `theta`) and any other non-ASCII character to a reversible `uXXXX` codepoint
escape, so an emitted problem is always valid ASCII and never contains a raw
non-ASCII identifier. Round-trip is exact for single-symbol constants (the realistic
case). Serialization (`to_dict` / `from_dict`) preserves the unicode name.

## [0.14.0] - 2026-07-10

Added — **binary interval operators `Until` (Ⓤ) and `Since` (Ⓢ) in the Isabelle/HOL
shallow embedding.** `to_isabelle_modal` / `isabelle_modal_theory` previously raised
`NotImplementedError` on `Until` and did not handle `Since` at all; both are now
emitted as **inductive least-fixpoint predicates** `muntil` / `msince` over the
one-step successor relation `n`:

- `muntil phi psi` is the least predicate closed under `psi w ⟹ muntil w` and
  `phi w ∧ n w v ∧ muntil v ⟹ muntil w`, so it denotes exactly the finite forward
  `n`-paths with `psi` at the endpoint and `phi` at every earlier point — the faithful
  counterpart of `satisfies_modal`'s depth-first path search (`_until_holds`).
  `msince` is the exact backward mirror over the converse of `n` (`_since_holds`). A
  plain interval reading over the henceforth closure `t` would be **unfaithful on
  branching / short-cut frames**; the least fixpoint is faithful on every frame.
- Using `Until` / `Since` now declares `n` (as `Next` does); when `Always` /
  `Eventually` co-occur, the `n_in_t` / `t_in_nstar` link axioms are emitted so the
  henceforth `t` denotes the closure of the *same* one-step relation the path-search
  operators read.

The `muntil` / `msince` definitions are **Isabelle-verified**: the live `check_theory`
gate loads a mixed-temporal theory and proves the strong-Until / Since fixpoint
equation, the base clause `Q → (P U Q)`, and strong-until reachability. Note this is
the HOL (Isabelle) embedding only — the first-order `qml_translate` still correctly
rejects `Until` / `Since`, which are **not** first-order definable (they need a
transitive-closure / fixpoint), and the `to_thf_modal` exporter remains the alethic
□/◇ fragment.

## [0.13.1] - 2026-07-03

Documentation correctness fix: the higher-order guide and the `hol/__init__`,
`isabelle_modal`, and `thf_modal` docstrings previously described FOL as "not even
semi-decidable". That is wrong — FOL validity is recursively enumerable (Gödel
completeness), so FOL and the standard first-order modal logics K/T/S4/S5 are
**undecidable but semi-decidable**; only full second-order validity is *not even
semi-decidable*. Corrected in the source text and in the German translation. No code
changes.

## [0.13.0] - 2026-07-03

Deep and shallow HOL embeddings with **machine-checked faithfulness proofs**,
reproducing Benzmüller, *Faithful Logic Embeddings in HOL — Deep and Shallow*
(arXiv:2502.19311). For each of four worlds-based non-classical logics the new
`unicode_fol_kit.hol.deepshallow` subpackage emits one self-contained Isabelle/HOL
theory carrying all three embeddings — a **deep** one (object syntax as a `datatype`
with a recursive `truthD`), a **maximal (heavyweight) shallow** one (every semantic
parameter explicit), and a **minimal (lightweight) shallow** one (accessibility and
valuation fixed as `consts`) — together with the `primrec` mappings `dpToMax` /
`dpToMin` and the theorems `faithful1a`/`faithful1b` (deep ↔ maximal),
`faithful2`/`faithful3` (↔ minimal in the fixed model) and `sound_min`, each closed
by a one-line `induct`. Unlike the existing emit-only shallow exporters, these
theories are **verified end to end** by the Isabelle runner (`check_theory`): a
green build means Isabelle's kernel discharged every faithfulness proof.

Added:

- `modal_faithfulness_theory` / `modal_to_deep` — propositional modal logic K.
- `intuitionistic_faithfulness_theory` / `int_to_deep` — intuitionistic
  propositional logic (Kripke semantics: preorder ≤, persistent valuation).
- `conditional_faithfulness_theory` / `counterfactual_to_deep` — Lewis
  counterfactual (sphere) logic, matching `semantics.conditional`.
- `relevant_faithfulness_theory` / `rel_to_deep` — relevant logic B (simplified
  Routley–Meyer semantics: normal worlds, Routley star, ternary relation), matching
  `semantics.relevant`.
- Isabelle-gated live tests that build each emitted theory and assert the kernel
  discharges the five faithfulness theorems, plus always-run structure tests.

The stack targets the propositional/schematic fragment (where induction over the
syntax datatype applies); the quantified decision path stays in
`unicode_fol_kit.hol.isabelle_modal`.

## [0.12.0] - 2026-07-03

The four families the documentation used to list as deliberately out of scope are
now first-class: relevant logic, hybrid logic, dependence / IF logic, and the
substructural pair (intuitionistic linear logic and the Lambek calculus). Each
ships with parser support, real semantics or a real proof system, hand-checked
tests cross-checked against existing oracles, and a documentation page.

### Added

- **Relevant logic B** (`semantics.relevant`) — the Priest–Sylvan *simplified*
  Routley–Meyer semantics for the basic affixing system **B** over the classical
  propositional syntax: `RelevantModel` (worlds, normal worlds, involutive Routley
  star, ternary accessibility at non-normal worlds), `rel_satisfies`, and a
  verified exhaustive countermodel search `rel_countermodel` / `rel_valid`
  (bounded, mirroring `int_valid`'s contract). The headline non-theorems come out
  right: `p → (q → p)`, explosion, disjunctive syllogism, Peirce, and even
  `p ∨ ¬p` are refuted, while the B-validities hold. Random formulas are
  cross-checked against the classical Z3 oracle (every classical countermodel is
  a one-world Routley–Meyer model). B is the decidable base; full **R** is
  undecidable (Urquhart 1984) and stays out of scope.
- **Hybrid logic H(@)** — nominals and the satisfaction operator inside the modal
  mode: `MSFLParser(modal=True)` now parses nominals (`i`, `here`) as formulas
  and `@i φ`; `KripkeModel` takes a `nominals=` assignment and `satisfies_modal`
  evaluates both constructs; the standard translation maps a nominal to a
  world-equality with a reserved `nom_…` constant, and the new
  `hybrid_is_valid(φ, frame="K"|"T"|"S4"|"S5")` decides hybrid validity via Z3.
  The ↓ binder is deliberately absent (it makes validity undecidable); the modal
  tableau rejects hybrid input with a clear error instead of guessing.
- **Dependence / IF logic** (`MSFLParser(dependence=True)` + `semantics.team`) —
  Väänänen-style **team semantics** over the toolkit's finite `Structure`s:
  dependence atoms `=(x, y)` (functional determination; `=(x)` constancy) and
  IF slashed existentials `∃y/{x} φ` (witness chosen uniformly in the slashed
  variables), with the splitting `∨`, strict `∃`, duplicating `∀`, and flat
  literals. `team_satisfies` / `team_models` evaluate; the fragment is honest —
  no `→`/`↔`, negation on atoms only, and no classical export (dependence logic
  is expressively second-order). Tested with flatness and downward-closure
  property tests against the Tarski evaluator and the classic `|dom| = 1`
  signalling facts.
- **Substructural logics** — two new sequent provers in `atp`:
  `MSFLParser(linear=True)` parses propositional **intuitionistic linear logic**
  (`⊗ & ⊕ ⊸ ! 𝟙`) and `ill_prove` / `ill_derivable` / `check_ill_proof` decide it
  by cut-free backward search — a complete decision procedure for the !-free
  fragment, honestly bounded when `!` occurs; `MSFLParser(lambek=True)` parses
  **Lambek-calculus** types (`• \ /` over categories like `NP`, `S`) and
  `lambek_prove` / `lambek_derivable` are a complete, terminating decision
  procedure for L (ordered, nonempty antecedents — `A, A\B ⊢ B` derives,
  `A\B, A ⊢ B` does not). Every found derivation is re-validated by its checker,
  and every derivable sequent's classical collapse is verified Z3-valid in the
  test suite.
- The frontier constructs render, verbalize (`to_english`), serialise
  (dict/JSON), and round-trip like every other node family; `exact_match` /
  `canonicalize` α-normalise the slashed binder (slash sets follow their
  enclosing binders' renames).

## [0.11.0] - 2026-07-02

Cross-logic parity for the natural-language / CCG translation-target constructs, plus a
capture-safety fix in the canonical form. The guiding principle: anything expressible in
classical FOL should also be expressible in the richer classical logics that extend it
(modal, second-order, and many-sorted), so a construct is no longer arbitrarily confined
to the plain `fol` mode.

### Added

- **Counting quantifier, concessive connective, and degree/cardinality terms across the
  classical modes.** `Count` (`∃≥n` / `∃≤n` / `∃=n`), `Contrast` (`Ⓒ`), `Measure` (`μ`),
  and `Cardinality` (`|{v : φ}|`) — previously accepted only by `MSFLParser()` — now also
  parse in **modal** mode (`MSFLParser(modal=True)`) and **second-order** mode
  (`MSFLParser(second_order=True)`), with identical semantics. A CCG-derived form that
  nests a counting quantifier under a modal or second-order operator — e.g.
  `B_a ∃≥3 x Pass(x)` ("a believes at least three x pass") — now parses and round-trips as
  a single string, not only as a hand-assembled AST.
- **MSFOL many-sorted parity: `SortedCount` and `SortedCardinality`.** The many-sorted mode
  (`MSFLParser(many_sorted=True)`) gains sort-annotated counterparts of the counting
  quantifier and the set-cardinality term — `∃≥n x:S φ` (`SortedCount`) and `|{v:S : φ}|`
  (`SortedCardinality`) — mirroring `SortedQuantifier`. `SortedCount` reduces to plain FOL
  by guarding the matrix with the sort predicate and reusing the distinct-witnesses
  encoding (so it is Z3-checkable); `SortedCardinality` is second-order and, like
  `Cardinality`, has no first-order export. `Contrast`, the `Measure` term, and `Xor` (`⊕`,
  previously excluded from MSFOL) are available in MSFOL too. Both new node types are
  exported from the package root.
- The fuzzy modes (FL / MSFL) deliberately **do not** gain these constructs: fuzzy logic is
  not a conservative extension of classical FOL (it reinterprets the connectives and its
  evaluator rejects comparison atoms), so counting/degree/cardinality/concession have no
  faithful truth semantics there. This is an intentional boundary, not an omission.

### Fixed

- **`exact_match` / `canonicalize` now α-normalize the counting and cardinality binders.**
  `Count` and `Cardinality` (and their new sorted variants) bind a variable, but the
  canonical form previously treated only `Quantifier` / `SortedQuantifier` / `Lambda` as
  binders. As a result `∃≥3 x P(x)` and `∃≥3 y P(y)` — α-equivalent — compared as unequal.
  They now canonicalize identically, while the op, the bound `n`, the sort, and the matrix
  stay significant.
- **Capture-safety of the canonical bound-variable rename.** The rename to canonical names
  `q0, q1, …` did not avoid free variables that happen to be named the same way, so the
  logically-distinct `∃x P(x)` and `∃x P(q0)` (where `q0` is free) both canonicalized to
  `∃q0 P(q0)` — a false positive in `exact_match` that violated equivalence-preservation.
  The rename now skips any canonical name that occurs free in the formula. The bug affected
  every binder (`Quantifier` / `Lambda` included) and was newly reachable through the
  counting binders; the fix covers all of them.

## [0.10.1] - 2026-06-30

### Fixed

- `unicode_fol_kit.__version__` now reports the actual package version (it lagged
  at `"0.9.0"` in the 0.10.0 release). The Sphinx / Read the Docs configuration
  reads this string for the documented version, so the docs version display is
  corrected as well.

## [0.10.0] - 2026-06-30

Natural-language → logic front-end support: attitude operators, a counting
quantifier, degree and cardinality terms, a concessive connective, a whole-file
Prover9 reader, TPTP single-quoted atoms, and name sanitisation. These are translation
targets and interchange aids for pipelines (e.g. CCG → logical form, or OWL → FOL)
that need a determinate, round-trippable representation of cardinal determiners,
degree comparatives, counting comparisons, reportative/desiderative attitudes, and
concessive coordination — and that ingest external problem files whose symbol names
are not native MSFLParser tokens.

### Added

- **Assertive and bouletic attitude operators** — `Says` (`Say_a φ`, *a asserts that
  φ*) and `Wants` (`Want_a φ`, *a wants it to be that φ*), modal `agent_prefix`
  operators alongside `Knows`/`Believes` (the agent is a β-bindable term, so
  `∀x (Speaker(x) → Say_x φ)` works). `Says` is **non-factive** and **non-doxastic**;
  `Wants` is **non-veridical** — each a minimal normal modality **K** over its own
  per-agent accessibility relation (`"Say:"+a` / `"Want:"+a`), with no frame
  conditions. Wired into the parser (`MSFLParser(modal=True)`), `satisfies_modal`, the
  modal tableau (`is_modal_valid`), `to_english`, and the dict/Unicode/LaTeX renderers.
- **Counting quantifier `Count`** — `∃≥n` / `∃≤n` / `∃=n` (at least / at most /
  exactly *n*). The bound *n* is carried **symbolically** (a `Number`, never expanded
  into single-letter variables), so an arbitrarily large *n* — `∃≥500 x …` — is
  represented exactly and coordinated counts compose as `And(Count(…), Count(…))`.
  First-order expressible: `to_z3` / `to_prover9` / `to_tptp` lower it to the standard
  distinct-witnesses encoding (a balanced conjunction tree, verified against Z3; the
  expansion is bounded to `n ≤ 500` — beyond that the exporters raise a clear error,
  while the symbolic node still round-trips for any `n`). Parses with the default
  `MSFLParser()`.
- **Degree term `Measure`** — `μ(entity, dimension)`, a first-class measure-function
  term for bare quantity comparatives (`μ(x, height) > μ(y, height)`); exports as the
  uninterpreted binary function `measure(entity, dimension)`.
- **Set-cardinality term `Cardinality`** — `|{v : φ}|`, the count of individuals
  satisfying `φ`, for faithful counting comparisons (`|{v : Votes(x, v)}| > |{v :
  Votes(y, v)}|`). It binds `v`; set cardinality is second-order, so it has **no**
  first-order export.
- **Concessive connective `Contrast`** — `P Ⓒ Q` (whereas / although / but),
  truth-functionally identical to `∧` but kept distinct so a front-end can preserve
  the concession instead of flattening it.
- **Whole-file Prover9 reader** — `load_prover9(path)` / `parse_prover9_problem(text)`
  read a Prover9 / LADR input file: `set` / `clear` / `assign` directives (recognised
  and skipped), `formulas(LIST). … end_of_list.` blocks, and bare top-level formulas,
  returning `Prover9Formula(role, formula)` records (the list name becomes the role).
  Completes the file-reading trio with `load_tptp` and `load_smtlib`.
- **TPTP single-quoted atoms** — the TPTP reader now accepts single-quoted functor
  names (`'http___example_org_Thing'(X)`), the form OWL→FOL dumps use for IRIs; the
  quotes are stripped and the `\'` / `\\` escapes unescaped. A 2.3 MB / 7198-formula
  OWL ontology dump reads end to end.
- **Name sanitisation for round-trippable rendering** — `sanitize_names(node)` /
  `sanitize_all(nodes)` rewrite imported symbol names to MSFLParser-legal tokens
  (predicates `[A-Z]…`, functions multi-letter lowercase, constants kept or put in the
  `c_…` form, variables `[a-z][0-9]*`) so that `parse(node.to_unicode_str())` round-trips.
  Already-legal names are unchanged; a returned `NameMapping` recovers the originals and
  keeps names consistent across a whole problem. (Verified: all 7198 formulas of the OWL
  dump round-trip after sanitisation.)

## [0.9.0] - 2026-06-29

A broad non-classical expansion: a native modal tableau, past-tense temporal logic,
more modal frames, four-valued FDE and a general matrix layer, fuzzy t-norms,
first-order intuitionistic and second-order search, sorted model finding, a
description-logic subpackage, and a cluster of non-classical neighbours.

### Added

- **Native modal tableaux — `unicode_fol_kit.atp.modal_tableau`.** A labelled,
  install-free tableau that decides the propositional box/diamond family (alethic
  `□`/`◇`, epistemic `K_a`, doxastic `B_a`, deontic `O`/`P`, one-step temporal `Next`)
  over the systems **K, T, D, B, K4, K45, S4, S5, KD45** plus per-family systems.
  `is_modal_valid` / `modal_decide` / `modal_countermodel` return valid / invalid /
  unknown with a Kripke counter-model **verified** against `satisfies_modal`. The
  classical `is_valid_tableau` / `prove_tableau` / `tableau_closed` now route modal
  inputs here instead of raising `ValueError`.
- **Past-tense temporal operators** — Prior tense logic: `Historically` (⒣), `Once`
  (⒫), `Previous` (⒴) and binary `Since` (⒮), the duals of `Always`/`Eventually`/
  `Next`/`Until` over the converse temporal relation. Covered in the parser,
  `satisfies_modal`, the standard translation, the qml embedding, and `to_english`.
- **More modal frames** — `B` (Brouwer), `S4.2` (convergent), `S4.3` (linear) decided
  by Z3 (`qml_is_valid`); `GL` (Gödel–Löb provability) via the Löb schema in the
  Isabelle / THF exporters (verified to discharge Löb's theorem in real Isabelle).
- **Finite-valued logical matrices + Belnap–Dunn FDE** — `semantics.matrix`:
  `TruthMatrix.from_functions` builds any finite matrix; ships `K3_MATRIX`,
  `LP_MATRIX` (reproducing the existing three-valued decisions) and the four-valued
  `FDE_MATRIX` (paraconsistent *and* paracomplete, with no logical truths).
- **Fuzzy t-norm selector + quantifier grounding** — `fuzzy_evaluate(…, tnorm=)` over
  **Łukasiewicz / Gödel / product** (new `semantics.tnorm`); `z3_fuzzy` decides the two
  piecewise-linear t-norms and **grounds quantifiers** over a finite domain, so
  quantified fuzzy validity / satisfiability is now decidable.
- **First-order intuitionistic Kripke search** — `int_valid` / `int_countermodel`
  search increasing-domain models for quantified formulas (bounded; the propositional
  fragment stays an exact decision).
- **Bounded second-order search** — `so_find_model` / `so_find_countermodel` /
  `so_is_satisfiable_finite` / `so_is_valid_finite` complement `satisfies_so`.
- **Many-sorted (MSFOL) model finding** — `find_model` / `find_countermodel` enumerate
  sort universes and return sorted `Structure`s.
- **Description logic ALC — `unicode_fol_kit.dl`.** Concept syntax (⊤ ⊥, ¬ ⊓ ⊔, ∃r.C
  ∀r.C), and a tableau reasoner (`concept_satisfiable`, `subsumes`, `equivalent`,
  `abox_consistent`) over general TBoxes / ABoxes, with TBox internalisation and subset
  blocking; cross-checked against the modal tableau.
- **Non-classical neighbours** — free logic (`semantics.free_logic`), public-
  announcement / dynamic epistemic logic (`semantics.dynamic_epistemic`),
  counterfactual conditionals (`semantics.conditional`, Lewis spheres), and
  circumscriptive non-monotonic entailment (`semantics.nonmonotonic`).
- **`isabelle_decide_fol` — decide classical FOL / MSFOL through Isabelle.** The
  counterpart of `isabelle_decide_modal` for the classical fragment: prove-battery →
  `nitpick` finite counter-model → UNKNOWN (common, since FOL is only semi-decidable),
  over `to_isabelle_fol` / `to_isabelle_msfol`. Returns a `FolVerdict`. Equality stays
  the **uninterpreted** `feq` / `fneq` of the embedding (no equality axioms assumed).
- **Linux CI for the Isabelle-backed tests** (`.github/workflows/isabelle-tests.yml`).
  Installs a real Linux Isabelle (cached) and runs the gated live tests on
  `ubuntu-latest` — the standing guarantee that the runner's primary (Linux) path
  works, since the dev box is Windows. Path-scoped + `workflow_dispatch`.

### Changed

- **`to_english` paraphrases the non-classical operators** (modal / temporal /
  epistemic / deontic / second-order / fuzzy) instead of falling back to glyphs; the
  fuzzy strong/weak/Łukasiewicz connectives are named so they do not read as their
  classical look-alikes. `naming` gained explicit modal / second-order mixing-error hints.

- **`isabelle_decide_modal` INVALID verdicts now carry a concrete counter-model.** For
  the propositional alethic fragment, `ModalVerdict.countermodel` is populated with a
  finite Kripke counter-model reconstructed from the toolkit's own `satisfies_modal`
  evaluator (`isabelle build` does not echo nitpick's model). `None` for fragments the
  bounded search does not cover — the certified verdict is unaffected.
- **Temporal `Always`/`Eventually` + `Next` refutation is sharp again.** The runner's
  *refute* theory now **defines** the henceforth relation as `t = rtranclp n` (the
  reflexive-transitive closure) instead of axiomatising it, so nitpick can construct the
  closure and genuinely refute a non-theorem — e.g. `Next(p) → Always(p)` is now
  `INVALID` instead of `UNKNOWN`. The *prove* theory keeps the axiom form (the battery
  needs it); both encode `t = n**`. (New `temporal_def` flag on `isabelle_modal_theory`.)

## [0.8.0] - 2026-06-28

### Added

- **Run a local Isabelle to actually *prove* the modal embeddings — `unicode_fol_kit.hol.isabelle_runner`.**
  The `hol` exporters only *emit*; this opt-in module turns "emit" into "proven / refuted" when an
  Isabelle/HOL install is present. `isabelle_decide_modal(φ, frame=…, mode=…)` decides validity by a
  two-step procedure, read off the build's exit code: (1) emit the lemma with a proof battery that
  brings the frame/domain axioms into scope (`using … by (blast | force | … | meson … | metis …)`) — a
  successful `isabelle build` means **VALID**; (2) otherwise emit `nitpick[expect = genuine]`, whose
  build succeeds **iff** a genuine finite counter-model exists — that means **INVALID**; (3) otherwise
  **UNKNOWN**. Sound (Isabelle's kernel certifies the proof; nitpick reports only genuine
  counter-models) and, necessarily, incomplete. The verdict is validated *differentially* against an
  independent brute-force Kripke oracle (`satisfies_modal`) across K/T/S4/S5 in the test suite.
  - `find_isabelle` / `isabelle_available` locate an install (explicit path → `UFK_ISABELLE_HOME` /
    `ISABELLE_HOME` → `isabelle` on `PATH` → a light scan); `check_theory(text, name)` builds any
    self-contained theory; `ModalVerdict` / `BuildResult` / `IsabelleInstall` carry the results.
  - **Linux/macOS is the primary path** — `isabelle` is invoked directly. **Windows** is also
    supported: the build is additionally routed through Isabelle's bundled Cygwin (Windows→`/cygdrive`
    path translation, launcher exec-bit fixup, `bin` on `PATH`). No install path is hard-coded —
    installations are discovered generically. Absent Isabelle raises a clear `IsabelleNotAvailable`;
    the live tests skip.
  - All re-exported at the package top level.

### Fixed

- **`to_isabelle_modal` emitted proofs could not discharge axiom-dependent validities.** A bare
  `axiomatization where r_refl: …` fact is not in Isabelle's default claset, so `by blast` / `by auto`
  / `by (metis …)` could not see it: every validity that *depends* on a frame/domain axiom (T, S4, S5,
  KD, KD45, the temporal closure, a domain regime) failed to prove even though the formula is valid and
  the theory sound (only the pure-K fragment, like the K axiom, went through). The `by`-style tactics
  now emit `using <frame/domain axioms> by …`. New `modal_axiom_names(φ, …)` exposes the axioms in
  scope, and `isabelle_modal_theory(…, proof=…)` accepts an explicit proof override.
- **`to_isabelle_k3lp` / `to_isabelle_k3lp_entailment` emitted a non-discharging proof.**
  `by (simp add: des_def)` does **not** close the validity lemma — `simp` cannot reduce `kneg v` /
  `kor v …` while the quantified truth-value `v` is abstract (e.g. the LP-valid `p ∨ ¬p` failed). The
  `∀` (valid) form is now discharged by exhausting each variable's three `tv` constructors
  (`case_tac` + `simp_all`); the `∃` (refutation) form by supplying the counter-valuation as `rule exI`
  witnesses computed at emit time. Every form is verified to build in real Isabelle.

### Changed

- **`to_isabelle_intuitionistic` now emits a real, Isabelle-checked proof for valid formulas.** The
  proof is verdict-dependent: an intuitionistically valid formula gets `using r_refl r_trans by
  (metis … | meson … | blast | auto)` that Isabelle discharges; a non-valid one is left `oops` (loads,
  claims nothing — see `int_countermodel`). Previously the lemma was always `oops`. The verdict is
  taken from the **decidable** S4 oracle `gmt_is_s4_valid` (Z3 on the GMT→S4 translation), *not* from
  `int_valid`'s default 3-world bound — which is incomplete (IPL's finite-model bound grows with the
  formula, so a non-theorem like `(p→q)∨(q→r)∨(r→p)` would otherwise be mis-emitted with a real
  proof that cannot close).

### Audit hardening

A multi-agent adversarial soundness audit of the new subsystem confirmed five issues (no false
*VALID* is possible — Isabelle's kernel rejects a proof of a false goal), all fixed and re-checked
against a live Isabelle:

- **Intuitionistic proof gated on the decidable oracle** (above) — was a real proof emitted for an
  IPL-*invalid* formula (theory then failed to build).
- **Atom-name collisions in the intuitionistic export.** An atom named `r` (or `w`/`v`/`u`) collided
  with the accessibility relation / frame-axiom variables, emitting a duplicate `consts r` (or an
  ill-typed axiom) so the theory never loaded — even for the valid `r → r`. `_isa_atom_name` now
  reserves the structural identifiers and de-collides (`r` → `p_r`).
- **Temporal closure now pinned faithfully.** When `Always`/`Eventually` co-occur with `Next`, the
  emitted henceforth relation `t` is now forced to equal the reflexive-transitive closure of the
  one-step `n` (`t ⊆ rtranclp n`, with the existing `t_refl`/`t_trans`/`n_in_t` giving the converse),
  matching `satisfies_modal`. Previously `t` could be any refl-trans superset of `n`, so a
  `satisfies_modal`-valid temporal induction `(p ∧ G(p→Xp)) → Gp` was spuriously refuted (a false
  *INVALID*); it is now never refuted (UNKNOWN — the closure fragment is a documented approximation).
- **`ModalVerdict.infra_error`.** An `UNKNOWN` whose build failed for an infrastructure reason
  (syntax / JVM / timeout / …) now carries a short signature, so a broken theory or environment is no
  longer indistinguishable from honest incompleteness. Never changes the verdict.

## [0.7.0] - 2026-06-28

### Added

- **Epistemic / doxastic frame systems in the first-order embedding.**
  `qml_is_valid` / `qml_equivalent` now take `systems={"epistemic": "S5", "doxastic":
  "KD45"}`, emitting per-agent frame axioms for the agent-indexed `Rk` / `Rb` relations
  — so e.g. factivity `∀x (K_x φ → φ)` is valid under a reflexive epistemic system. This
  makes the FO path symmetric to the THF exporter (which already had `systems=`).
- **Quantified modal logic (QML) via shallow embeddings.** Object quantifiers `∀x` /
  `∃x` under a modality, with the domain-regime semantics that decide the Barcan
  formulas:
  - **Semantics** — `KripkeModel` now takes per-world object domains (`domains={w: …}`
    for varying, `domain=[…]` for constant), and `satisfies_modal` interprets `∀x` /
    `∃x` *actualistically* (at a world `w` they range over `D_w`). Barcan
    (`◇∃x A → ∃x ◇A`) and converse Barcan are valid/invalid exactly as the domains
    vary. Backward compatible (omit the domains for the propositional fragment).
  - **(A) First-order shallow embedding** (`unicode_fol_kit.fol.qml`): `qml_translate`
    (with the existence predicate `E!` relativising actualist quantifiers + world/object
    sort guards), `qml_axioms`, and `qml_is_valid` / `qml_equivalent` decide validity /
    equivalence with Z3 per domain regime (`constant` / `increasing` / `decreasing` /
    `varying`) and frame (K/T/S4/S5/KD/KD45). Sound but bounded-incomplete (first-order
    modal logic is undecidable). The regime↔Barcan correspondence (BF ⇔ decreasing,
    CBF ⇔ increasing, constant ⇔ both) is cross-checked against exhaustive Kripke-model
    enumeration over every regime.
  - **(B) Higher-order shallow embedding** — `to_thf_modal` emits a Benzmüller-style
    TPTP **THF** problem (lifted `mbox`/`mdia`/`mforall`/`mexists`/`mvalid` + frame and
    domain axioms) for an external higher-order prover (Leo-III, Satallax); 
    `to_isabelle_modal` emits an Isabelle/HOL skeleton. Alethic □/◇ fragment.
  - All re-exported at the package top level; `BARCAN` / `CONVERSE_BARCAN` are provided
    as the standard litmus formulas.
- **`⊕L` / `⊕R` (exclusive-or) rules in the sequent calculus** (`A⊕B ≡ ¬(A↔B)`),
  closing the one connective that had no inference rule in either checker.
- **HOL / Isabelle / THF exporters for all non-fuzzy logics** (new
  `unicode_fol_kit.hol` subpackage) — Benzmüller-style shallow semantical embeddings,
  emitted as complete problem files for an external prover (the toolkit emits; it does
  not run Leo-III / Satallax / Sledgehammer, and FOL / FO-modal / SOL are undecidable, so
  emission means "a sound problem a prover *may* discharge", never "decided"):
  - `hol.isabelle_modal.to_isabelle_modal` — a **real, loadable** Isabelle/HOL theory
    (`theory … imports Main begin … end`, all lifted operators, frame + domain axioms,
    the formula lifted into the embedding, a real `lemma`) for the **full modal family**:
    alethic, epistemic/doxastic over **agent-indexed** relations, deontic, temporal.
    Replaces the old alethic-only skeleton that emitted the lemma inside a comment.
  - `hol.thf_modal.to_thf_modal_full` — the full-modal-family TPTP **THF** export
    (agent-indexed epistemic/doxastic, deontic, temporal), extending the alethic-only
    `qml.to_thf_modal`; self-contained (every relation the macro block references is declared).
  - `hol.classical` (FOL + MSFOL), `hol.manyvalued` (K3 / LP, cross-checked against the
    three-valued evaluator), `hol.secondorder` (native HOL predicate quantification),
    `hol.intuitionistic` (Gödel–McKinsey–Tarski → S4 → HOL, cross-checked against
    `int_valid`) — each → THF and Isabelle.
- **First-class agent terms for epistemic/doxastic operators.** The `agent` of
  `Knows` / `Believes` is now a **term** (Variable or Constant), a structural child, so
  it is reached by `free_variables` / substitution / β-reduction and can be a quantified
  variable — `∀x (Student(x) → K_x φ)` (a quantified subject, "every student who…")
  finally works: the agent is the bound `x`, not a baked-in relation-name suffix.
  - The Kripke evaluator uses **per-agent** accessibility relations (one agent can know
    what another does not); object quantifiers ground a bound agent before the modality
    is reached.
  - The first-order shallow embedding emits an **agent-indexed ternary** relation
    `Rk(agent, w, v)` / `Rb(agent, w, v)`, so a bound agent genuinely quantifies over
    agents (epistemic/doxastic relations are plain `K` — no frame axioms yet).
  - Parser convention: a free `K_a` is a *named* agent (→ Constant); an agent bound by an
    enclosing quantifier (`K_x` under `∀x`) stays a Variable. A bare string passed to the
    constructor is coerced to a Constant (backward compatible).

### Fixed

- **HOL/THF/Isabelle exporters: distinct symbols can no longer collapse to one name.**
  A de-colliding resolver (`_ThfNames` / `_IsaNames` / the second-order and classical
  resolvers) guarantees each distinct `(kind, name, arity)` symbol gets a unique emitted
  functor / `consts`, and a predicate used at two arities is two symbols. Fixes a
  **soundness hole** where a non-valid formula could be emitted as valid — e.g. `□Ab →
  □ab` collapsing to the tautology `□ab → □ab` (also in the shipped `qml.to_thf_modal`)
  — and the duplicate / ill-typed declarations that made `to_isabelle_so` / the modal
  Isabelle theories non-loadable.
- **`to_isabelle_modal` is now the real exporter everywhere.** The top-level
  `to_isabelle_modal` (and `fol.qml.to_isabelle_modal`) delegate to the complete
  `unicode_fol_kit.hol.isabelle_modal` implementation (a loadable theory with a genuine
  `lemma`), instead of the old alethic-only skeleton that emitted the lemma in a comment.
- **`substitute` is now capture-avoiding for a re-binding quantifier.** Substituting a
  `Variable` (as `satisfies_modal` does when grounding an object quantifier) no longer
  leaks past an inner quantifier that re-binds the same name: `substitute(∃x A(x), x, a)`
  now correctly returns `∃x A(x)` unchanged. This fixes a **soundness bug in the modal
  evaluator**, where a shadowed quantifier (e.g. `∀x ∃x A(x)`, also under modalities)
  evaluated to the wrong truth value. (The `Lambda` branch already stopped at a rebinding
  binder; the `Quantifier` / `SortedQuantifier` branches now do too.)
- **QML rejects an unknown `mode`.** `qml_translate` / `qml_is_valid` / `qml_equivalent`
  raise `ValueError` on an unrecognised domain regime (e.g. a mis-capitalised
  `'Increasing'`) instead of silently treating it as constant-domain and returning a
  wrong validity verdict — matching the existing `frame` validation.
- **THF export: `possibilist` now emits the `const_dom` axiom.** Since the FO embedding
  treats `possibilist` as a constant domain, the THF export does too (its actualist
  `mforall`/`mexists` macros would otherwise model a varying domain), keeping the two
  embeddings in agreement.
- **THF export: `=` / `≠` are now uninterpreted predicates, not primitive HOL identity.**
  `to_thf_modal` previously rendered equality as rigid HOL `=`, diverging from
  `satisfies_modal` and the FO embedding (which key `=` / `≠` as ordinary
  world-relativized predicates) — so e.g. `∀x. x=x` was a THF theorem but
  Kripke-falsifiable. All three embeddings now agree.

### Internal

- **Retired the parser-equivalence oracle.** The registry-assembled parser was pinned
  during migration by a byte-for-byte equivalence test against the legacy hand-written
  per-mode `.lark` grammars + `*Transformer` classes. With that equivalence long
  established, the reference pipeline was removed: the six per-mode grammar files
  (`fol`/`msfol`/`msfl`/`fl`/`modal`/`so.lark`) and the legacy transformer classes are
  gone; the registry self-assembly + grammar-structure guards remain. Only
  `terminals.lark` survives (imported by the generated grammar at runtime).
- **Shared symbol-name de-collision** (`fol/_symbol_names.py`): the `dedupe` helper and
  the THF/Isabelle resolver, previously copy-pasted across the exporters, are now one
  `SymbolNames` base + `dedupe` used by the THF, Isabelle, classical, and second-order
  exporters.
- **Agent token parsing reuses the scope pass.** The epistemic/doxastic agent is parsed
  as a Variable and resolved to bound-Variable / free-Constant by `resolve_agent_variables`
  (mirroring `resolve_lambda_scope`), instead of re-deciding variable-vs-constant with a
  hand-copied lexer regex.
- **Adversarial audit of the proof checkers.** A multi-agent audit ran independent
  oracles against every accepted proof/derivation of the Fitch and sequent checkers
  across all logics (~75 hand-built adversarial constructions plus >1M fuzzed cases)
  and found **no soundness hole**. Follow-up hardening from the audit's coverage
  findings: added regression tests pinning the `verify_proof` robustness guards (a
  clean `ProofResult(ok=False)` instead of a crash on a non-`Line` premise or subproof
  assumption) and the mixed quantifier-spelling normalisation (`'forall'` vs `∀`); and
  extended the sequent test corpus so the randomised mutation / Z3 audit now also
  exercises `Cut`, weakening, contraction, `∨L`, `↔L`/`↔R`, `∃L`, and `⊕L`/`⊕R`.
- **Independent differential test harnesses promoted into the committed suite**, so the
  checkers are cross-checked against oracles *other* than the ones they use internally:
  - the alethic modal Fitch checker against brute-force Kripke-frame enumeration
    (`tests/test_modal_differential.py`) — independent of its standard-translation/Z3
    path, covering the K/T/S4/S5 frame-sensitivity facts;
  - the second-order sequent rules against `satisfies_so` (`so_valid_tiny`) under a
    randomised mutation audit (Z3 cannot evaluate second-order nodes);
  - the object-level eigenvariable freshness condition (`∀R`/`∃L`) under randomised
    fresh/non-fresh fuzzing.

## [0.6.0] - 2026-06-27

A large reasoning-and-interoperability release: a Fitch natural-deduction checker and
backtracking prover, a Gentzen **LK** sequent calculus (with second-order rules) and an
intuitionistic **LJ** calculus, analytic tableaux, a finite model finder, truth tables,
reverse importers for TPTP / Prover9 / Z3-SMT-LIB, intuitionistic Kripke semantics, and
formula verbalization. All additive.

### Added

- **Fitch-style natural-deduction proof checker** (`unicode_fol_kit.atp.fitch`) —
  `Proof` / `Subproof` / `Line` / `Justification` proof objects (frozen, hashable,
  JSON-serialisable) plus `check_proof` / `verify_proof`, all re-exported at the
  package top level. The checker is *sound*: it returns `True` only when every
  line genuinely follows by the cited rule and the proof's premises entail its
  conclusion; `verify_proof` reports the certified sequent and the first failing
  line with a reason.
  - **Classical FOL / MSFOL** (`logic="fol"`/`"msfol"`) is checked by a syntactic
    rule table: the connective rules (`∧I`/`∧E`, `∨I`/`∨E`, `→I`/`→E`, `↔I`/`↔E`,
    `¬I`, `⊥I`/`⊥E`, `¬E` double-negation, `RAA`, `Reit`), the quantifier rules
    (`∀I`/`∀E`, `∃I`/`∃E`) with the eigenvariable side-conditions enforced via a
    capture-avoiding substitution, and equality (`=I`/`=E`, certified against Z3).
    Citation accessibility is enforced (no reaching into a closed sibling
    subproof) and discharge rules are checked against the proof's *open
    assumptions*. `⊥` is the reserved logical constant `FALSUM`.
  - **Three-valued K3 / LP** (`logic="K3"`/`"LP"`) certify each step against the
    many-valued decision procedure (`semantics.manyvalued.entails`), so the
    paraconsistency facts hold: LP rejects modus ponens, the disjunctive
    syllogism, and explosion; K3 has no zero-premise theorems. Propositional
    fragment.
  - **Modal family** (`logic="K"`/`"T"`/`"S4"`/`"S5"`) certifies each step by the
    standard translation to FOL plus the frame axioms, decided by Z3. Knowledge
    (`Knows`, S5) is factive; belief (`Believes`, KD45) and obligation
    (`Obligatory`, KD) are not. Propositional fragment; temporal and quantified
    modal input are rejected.
  - **Rendering** — `render_fitch` (Unicode/ASCII scope bars, line-number gutter,
    justification column; also `proof.to_fitch()`) and `render_latex_fitch`
    (self-contained LaTeX `array`; also `proof.to_latex_fitch()`).
  - Tested with hand-derived proofs per rule, soundness guards for the broken
    cases, and a randomised audit that checks every accepted proof line-by-line
    against the Z3 / resolution oracles.
- **Gentzen sequent-calculus checker** (`unicode_fol_kit.atp.sequent`) — a
  two-sided **LK** derivation checker re-exported at the package top level:
  `Sequent` / `Derivation` / `Comprehension` / `SequentResult`, the helpers
  `sequent` / `derive` / `axiom`, and `check_sequent_proof` / `verify_sequent_proof`
  / `render_sequent_proof`. A sequent `Γ ⊢ Δ` (multisets, read `⋀Γ → ⋁Δ`) is
  derived by a tree of rules; the checker verifies each step.
  - Rules: `Ax`, structural `WL`/`WR`/`CL`/`CR`/`Cut`, the connective rules
    (`¬`, `∧`, `∨`, `→`, `↔`, each L and R), the first-order quantifier rules
    (`∀L`/`∀R`, `∃L`/`∃R`, with the eigenvariable condition on `∀R`/`∃L`), and the
    **second-order** rules `∀²L`/`∀²R`, `∃²L`/`∃²R`. `∀²L`/`∃²R` instantiate a bound
    predicate variable with a comprehension term `λx̄.ψ` (a `Comprehension`,
    arity-checked, capture-avoiding); `∀²R`/`∃²L` use a fresh predicate
    eigenvariable. This reaches the second-order fragment (`second_order=True`),
    which has no first-order / SMT encoding.
  - Sound but, for full second-order logic, necessarily **not a complete prover**
    (second-order validity is not r.e.). Tested with hand derivations per rule,
    soundness guards, a randomised mutation audit that re-checks every accepted
    derivation node-by-node against Z3 (first-order fragment), and `satisfies_so`
    spot-checks over small finite models (second-order fragment).
- **Analytic tableaux** (`unicode_fol_kit.atp.tableau`) — `is_valid_tableau`,
  `prove_tableau`, `tableau_closed`, and `tableau_model`, re-exported at the top
  level. A fourth proof method (beside resolution, Fitch, and the sequent calculus):
  the signed-free α/β/γ/δ rules, a branch closing on `φ`/`¬φ`. Decidable and complete
  for the propositional fragment; first-order γ-instantiation is bounded (`max_terms`
  / `max_steps`). An *open* branch is returned as a countermodel by `tableau_model`.
- **Finite model finder** (`unicode_fol_kit.semantics.modelfinder`) — `find_model`,
  `find_countermodel`, `is_satisfiable_finite`, and `is_valid_finite`. Brute-force
  enumeration of finite `Structure`s (domain `1..max_size`) checked with the Tarskian
  evaluator — the Mace4-style partner of the provers (a valid entailment has no
  countermodel; an invalid one usually a small finite one). Bounded by
  `max_candidates`.
- **Truth tables** (`unicode_fol_kit.semantics.truthtable`) — `truth_table` returning
  a `TruthTable` (Markdown `render`, `is_tautology`/`is_contradiction`/`is_satisfiable`),
  plus `is_tautology` / `is_contradiction` / `is_satisfiable_tt`, over **classical**,
  Kleene **K3**, and Priest **LP** value sets (cross-checked against Z3 for classical).
- **Intuitionistic propositional logic** (`unicode_fol_kit.semantics.intuitionistic`) —
  `IntKripkeModel` with monotone Kripke `forces`, and `int_valid` / `int_countermodel`
  that decide intuitionistic validity by Kripke-model search (the logic has the
  finite-model property). Excluded middle, double-negation elimination, and Peirce's
  law are reported invalid with explicit countermodels; every intuitionistic validity
  is also classically valid (cross-checked).
- **Intuitionistic sequent calculus LJ** (`unicode_fol_kit.atp.lj`) — `check_lj_proof`
  / `verify_lj_proof`, re-exported at the top level. Gentzen **LJ** is the LK calculus
  (it reuses the same `Sequent` / `Derivation` data model) restricted to **at most one
  succedent formula** — the change that makes excluded middle / double-negation
  elimination / Peirce's law underivable. Rules: `Ax`, structural `WL`/`WR`/`CL`/`Cut`,
  `¬`/`∧`/`→`/`↔` (L and R), the split disjunction-right `∨R1`/`∨R2` and `∨L`, and the
  quantifier rules `∀L`/`∀R`, `∃L`/`∃R`. Accepted derivations are cross-checked against
  the intuitionistic Kripke decision procedure and classical Z3 validity.
- **Verbalization** (`unicode_fol_kit.fol.verbalize`) — `to_english`, an English
  paraphrase of a formula (a readability aid, not a parse inverse).
- **Fitch proof *searcher*** (`unicode_fol_kit.atp.fitch_search`) — `find_fitch_proof`,
  `fitch_prove`, and `is_valid_fitch`, re-exported at the package top level. A
  goal-directed, **iterative-deepening backtracking** search over the classical
  propositional + first-order natural-deduction rules (introduction rules, ∨/∃
  elimination by case split, backward chaining, ex falso, and reductio/RAA — which
  makes it complete for the propositional fragment). It builds an actual `Proof`
  that is re-validated by `check_proof` before being returned, so it is **sound by
  construction**: a search/assembly bug can only make it fail to find a proof, never
  return an unsound one. Like the resolution prover it is sound but, under its depth
  bound, incomplete (`None`/`False` = "not found within `max_depth`"). Tested with
  curated theorems/non-theorems and a randomised cross-check that every found proof
  is Z3-valid.
- **Reverse importers for TPTP, Prover9, and Z3/SMT-LIB** — the inverses of
  `to_tptp` / `to_prover9` / `to_z3`, all re-exported at the package top level:
  - **TPTP** (`unicode_fol_kit.fol.tptp_input`): `parse_tptp_formula` (one bare
    FOF/CNF formula → `Node`), `parse_tptp` (a whole problem → a list of
    `TptpFormula(name, role, formula)`), and `load_tptp` (a `.p`/`.tptp` file), via
    a dedicated Lark grammar. Round-trips `to_tptp`; `%` and `/* */` comments are
    ignored; predicates are re-capitalised (TPTP lowercases them); typed
    `tff`/`thf` and `include` are out of scope.
  - **Prover9/LADR** (`unicode_fol_kit.fol.prover9_input`): `parse_prover9`,
    following `set(prolog_style_variables)` to match `to_prover9`'s output (a
    trailing `.` is accepted). `Xor` round-trips to its `(a|b) & -(a&b)` desugaring.
  - **Z3** (`unicode_fol_kit.atp.z3_input`): `from_z3` (a `z3.ExprRef` → `Node`)
    and `parse_smtlib` / `load_smtlib` (SMT-LIB2 via Z3's own parser). Conversion is
    meaning-preserving (Z3 collapses variables/constants/numbers onto one
    uninterpreted sort, so a free variable returns as a `Constant`).
  - Tested by round-trip over random formulas (`parse(node.to_X()) == node`) for
    TPTP/Prover9 and by logical equivalence (`is_valid(Iff(node, from_z3(node.to_z3())))`)
    for Z3, plus curated problem-file and SMT-LIB cases.

## [0.5.2] - 2026-06-26

### Added

- **Predicate-aligned string match** (`unicode_fol_kit.eval.predicate_match`) —
  `match_predicates`, `formulas_are_matched_identical`, and
  `formulas_are_identical`, re-exported at the package top level. A lexical
  (string-level) evaluation notion for NL→FOL: `match_predicates` greedily
  renames each predicate/function symbol in a predicted formula to the
  lexically-closest symbol in the reference (by **normalised Levenshtein
  distance**, accepting matches at or below a `max_norm_distance` threshold,
  default `0.6`), so a structurally-correct answer that merely chose different
  predicate names is not penalised. `formulas_are_identical` is the plain
  whitespace- and case-insensitive string equality; `formulas_are_matched_identical`
  combines the two (realign predicates, then compare). This is **complementary**
  to the AST-level `exact_match`: the canonical match quotients out α-renaming /
  commutativity / associativity / double negation but treats different predicate
  names as a mismatch, whereas this matcher quotients out predicate-name (and
  whitespace/case) differences but not the structural rewrites — the two are
  typically reported as separate metrics. The Levenshtein distance is computed in
  pure Python, so **no new dependency** is introduced; the matcher is
  parser-independent and also applies to raw, not-yet-parseable model output.

## [0.5.1] - 2026-06-24

### Added

- **`check_logical_entailment_vampire`** — entailment checking via the
  [Vampire](https://vprover.github.io/) theorem prover, a TPTP-based companion to
  the existing Prover9 backend. Premises are emitted as TPTP `axiom`s and the
  conclusion as a `conjecture`; the path to the Vampire executable is passed as
  the `vampire_path` argument, and a `SZS status Theorem` result means the
  entailment holds. Classical FOL only (the same fragment `to_tptp` supports).
  Pass `use_wsl=True` to drive a Linux Vampire installed in WSL from a Windows
  host (Vampire is launched via `wsl.exe`, with automatic `wslpath` translation of
  the temp-file path).

## [0.5.0] - 2026-06-24

Adds an NL→FOL **evaluation** toolkit and broad **non-classical logic** coverage —
modal/temporal/epistemic/deontic logic with Kripke semantics, three-valued
(Kleene/Priest) logic, and second-order quantification with finite-model
semantics. All additive; no breaking changes.

### Added

- **`unicode_fol_kit.eval`** — `canonicalize` / `exact_match` (a fair "canonical
  exact match" that quotients out bound-variable renaming, commutativity/
  associativity, operand duplication, and double negation while staying logically
  equivalent), and `validate` / `is_wellformed` / `validate_text` /
  `ValidationReport` (free variables, inconsistent predicate/function arity,
  leftover lambda nodes, parseability of raw model output).
- **Modal / temporal / epistemic / deontic logic** (`MSFLParser(modal=True)`):
  node classes `Box`, `Diamond`, `Knows`, `Believes`, `Always`, `Eventually`,
  `Next`, `Until`, `Obligatory`, `Permitted` with surface syntax `□ ◇`, `K_a` /
  `B_a`, `Ⓖ Ⓕ Ⓝ Ⓤ`, `Ⓞ Ⓟ`. Kripke-model semantics (`KripkeModel`,
  `satisfies_modal`, `reflexive_transitive_closure`) and a relational
  `standard_translation()` to classical FOL so Z3/resolution can decide modal
  validity. Propositional/ground (v1).
- **Many-valued logic** (`unicode_fol_kit.semantics.manyvalued`): three-valued
  strong-Kleene evaluation `kleene_value` over {0, ½, 1}, and `is_valid` /
  `is_satisfiable` / `entails` with selectable designated values for Kleene
  **K3** (`{1}`) and Priest **LP** (`{½, 1}`, paraconsistent). `kleene_value` /
  `DESIGNATED` are also re-exported at the package top level.
- **Second-order / monadic-second-order quantification** (`MSFLParser(second_order=True)`):
  `SecondOrderQuantifier` (`∀P` / `∃P`, arity inferred from the body) with
  finite-model semantics (`satisfies_so`) that enumerates relations over a finite
  domain. Higher-order *terms* remain available via the existing lambda layer;
  full HOL types are out of scope.
- **LaTeX import** — `parse_latex()` reads a LaTeX-math formula (the inverse of
  `to_latex()`) and `latex_to_unicode()` does the LaTeX→Unicode translation alone;
  accepts the exact `to_latex()` output (round-trips) and common hand-written synonyms.

### Internal

- **Operator registry** — operators are now fully self-describing, decoupling
  rendering *and* parsing from the central modules:
  - *Rendering:* each operator registers its glyph, LaTeX markup, precedence, and
    fixity via `register_operator()`; the Unicode and LaTeX renderers are driven
    generically from the registry (no per-operator branches, no hand-maintained
    dispatch tables).
  - *Parsing:* each operator also registers its grammar fragment + transform via
    `register_parser_op()`. `MSFLParser` now assembles BOTH the Lark grammar and
    the transformer for every mode (FOL/MSFOL/MSFL/FL/modal/second-order) from the
    registry — there is no longer a hand-written per-mode transformer or a
    hand-loaded `.lark` grammar on the runtime path.
  - Output and parsed ASTs are byte-identical to before (guarded by a
    legacy-vs-registry equivalence test across a 190-formula × 6-mode corpus).
    Adding an operator — or a whole new logic — is now a self-contained registry
    entry in the operator's own module, with no edit to the renderers, the parser,
    or any shared grammar file.
- **Hardening of the new evaluators.**
  - The three-valued enumeration (`is_valid` / `is_satisfiable` / `entails`) now
    scores each assignment with a compiled evaluator built once from the formula
    (no per-assignment AST walk or atom re-rendering), and refuses to start an
    enumeration above `manyvalued.MAX_MODELS` rather than hanging.
  - Second-order `satisfies_so` refuses a `∀P` / `∃P` whose `2 ** (n ** k)`
    relation space exceeds `secondorder.MAX_RELATIONS`, with a clear error.
  - Added seeded, randomized cross-checks: the compiled three-valued path against
    the reference `kleene_value` on every assignment; strong-Kleene algebraic
    identities and the K3-vs-LP headline facts; second-order `∀P φ ≡ ¬∃P ¬φ`
    duality and the agreement of `satisfies_so`'s classical core with the
    first-order Tarski evaluator; render→parse round-trips over random FOL, modal,
    Łukasiewicz, and second-order formulas; and a whole-tree `tree_str` / `to_dot`
    coverage check over every node type.
  - Łukasiewicz-algebra cross-checks for the fuzzy evaluator (strong/weak
    De Morgan, double negation, the residuum `a → b ≡ ¬a ⊕ b`, and the defining
    adjunction `a ⊗ b ≤ c ⟺ a ≤ b → c`) over random + boundary-grid valuations.
  - Eval cross-checks against the independent Z3 oracle: `canonicalize` is
    equivalence-preserving, `exact_match` absorbs the rewrites it should and never
    merges Z3-inequivalent formulas, and `validate` flags free variables, arity
    clashes, and leftover lambdas.
  - A README example runner executes every `python` block in the docs (cumulative
    namespace) so the documentation stays in lock-step with the code.

## [0.4.0] - 2026-06-23

A large feature release adding model-theoretic and many-valued semantics, an
in-process theorem prover, more solver back-ends, and lambda/normal-form tooling,
plus a set of correctness fixes. **Includes one breaking change** (see *Changed*).

### Added

- **Tarskian model theory** (`unicode_fol_kit.semantics.tarski`): define a
  `Structure` (a "world" with a domain of individuals and interpretations of
  constants, functions, predicates, and — for MSFOL — sorts) and compute a
  formula's truth value with `satisfies()` / `models()` / `term_value()`.
  Equality is built in; sorted quantifiers range over their sort universe.
- **Łukasiewicz fuzzy evaluator** (`fuzzy_evaluate`): the truth degree in [0, 1]
  of an FL/MSFL formula under a valuation (`∀` = inf, `∃` = sup).
- **Fuzzy satisfiability / validity** via Z3 reals: `fuzzy_is_satisfiable`,
  `fuzzy_is_valid`, `fuzzy_get_model`, `degree_expr`.
- **Arithmetic-aware Z3 translation**: `to_z3_arith`, `is_satisfiable_arith`,
  `is_valid_arith`, `get_model_arith` interpret `+ - * /` and the comparisons
  over Z3 reals/integers (the default `to_z3` keeps them uninterpreted).
- **Built-in first-order resolution prover** (`unicode_fol_kit.atp.resolution`):
  `prove`, `is_valid_resolution`, `to_clauses`, `refute` — sound entailment and
  validity checking in-process, without an external prover. Deliberately
  incomplete under a step bound (never reports a non-theorem as proved);
  `=` is treated as an uninterpreted predicate.
- **Lambda tooling**: `eliminate_lambdas` (beta-eta normalise and verify
  lambda-free), `reduce_trace`, `beta_reduce_step`, `has_lambdas`.
- **Normal forms**: `to_dnf` (equivalence-preserving) and `to_tseitin_cnf`
  (equisatisfiable, avoids the distributive blow-up).
- **Robinson unification**: `unify` (most general unifier with occurs-check) and
  `apply_subst`.
- **Command-line interface**: `python -m unicode_fol_kit "<formula>" --mode … --to …`.
- **Typing**: a `py.typed` marker (PEP 561).
- **AST helper**: `Node.map_children`, the single structural-recursion engine.

### Changed

- **BREAKING — AST nodes are now frozen dataclasses.** Every node is immutable
  and **hashable**, so nodes can be put in sets, used as dict keys, and
  deduplicated.
- **BREAKING — `Function.args` and `Atom.args` are now `tuple`s, not `list`s.**
  Construction stays lenient: a list passed to the constructor is coerced to a
  tuple, so `Atom("P", [x])` still works and `node == node` comparisons are
  unaffected. Code that relied on `.args` being a *list* (in-place mutation,
  `isinstance(node.args, list)`, or comparing `node.args == [...]`) must switch
  to tuples.

### Fixed

- `Xor.to_tptp` emitted `~|` (TPTP **NOR**); now emits `<~>` (correct XOR /
  non-equivalence).
- TPTP arithmetic comparisons (`<`, `>`, `≤`, `≥`) are now emitted as prefix
  dollar-word predicates (`$less(a, b)`), not as invalid infix expressions.
- Prover9 export: quantified variables are uppercased to match the emitted
  `set(prolog_style_variables)`; nullary predicates render as bare propositional
  atoms instead of the invalid `P()`.
- `to_latex` escapes the underscore in `c_`-prefixed constants (otherwise read as
  a LaTeX subscript).
- Prover9 entailment: the temporary input file is no longer leaked when the
  `prover9_path` is invalid (now cleaned up in a `finally`).
- Several README inaccuracies (clone URL, "three" vs "four" parser modes, the
  exception class raised on mixing same-level connectives, the `Quantifier`
  AST-table annotation), and the `formulas_are_equivalent` / `is_valid`
  docstrings.

### Documentation

- Clarified that `to_fol` / `to_msfol` is a classical **Boolean projection**
  (the strong and weak Łukasiewicz connectives both collapse to `And`/`Or`), not
  a fuzzy-preserving translation — use `fuzzy_evaluate` / the fuzzy Z3 solver for
  many-valued degrees.

### Internal

- Refactored the duplicated structural recursions (`free_variables`,
  substitution, beta/eta reduction, scope resolution, `to_msfol`/`_relativize`,
  term substitution) onto the shared `Node.map_children` / `_child_nodes`
  helpers, removing the per-node `isinstance` chains while preserving the
  binder-aware special cases and the public `TypeError` contracts.

## [0.3.1] - earlier

- LaTeX export, normal forms, Horn check, Z3 models, traversal API, Graphviz export.

## [0.3.0] - earlier

- `to_unicode_str()` with parser round-trip.

## [0.2.1] - earlier

- README patch release.
