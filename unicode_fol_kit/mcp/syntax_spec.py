"""Machine-readable syntax specification, served over MCP.

An LLM writing formulas for this kit needs the rules it is about to break —
and it needs them AT THE MOMENT it breaks them, not buried in a system
prompt it saw ten thousand tokens ago. This module is the retrievable form
of the kit's surface syntax: naming conventions, operator precedence,
dialect selection, the counting quantifier, and the documented failure modes
of LLM-generated formulas, each as a small JSON payload the model can fetch
by topic when a parse fails.

**The spec cannot drift from the parser.** Every ``EXAMPLES`` entry names the
dialect it is written in and what it must render back as, and
``tests/test_syntax_spec.py`` parses every single one and compares. A rule
here that the parser does not actually implement is therefore a failing test,
not a lie an agent discovers at 3am. Wherever a fact is already derivable
from live kit objects (the dialect signal table, the parser mode ladder), it
is READ from them rather than restated.

The intended loop is: generate → parse fails → the error names a topic →
``syntax_spec(topic=...)`` → regenerate. That closes the correction loop
without inflating every prompt with the full grammar, which matters when the
generating model is a local vLLM deployment paying for every prompt token on
every one of thousands of classes.
"""

from typing import Dict, List, Optional

__all__ = ["syntax_spec", "SPEC_TOPICS", "EXAMPLES"]

SPEC_TOPICS = (
    "overview", "naming", "dialects", "operators", "quantifiers",
    "counting", "chemistry", "errors",
)

#: (label, dialect, source text, expected unicode rendering). The single
#: source of truth for every example shown in any topic below — the test
#: module parses each one, so an example can never quietly go stale.
EXAMPLES = (
    ("variable-vs-constant", "fol", "P(x) ∧ P(alice)", "P(x) ∧ P(alice)"),
    ("function-term", "fol", "P(f(x))", "P(f(x))"),
    ("equality", "fol", "alice = bob", "alice = bob"),
    ("universal", "fol", "∀x (Dog(x) → Animal(x))", "∀x (Dog(x) → Animal(x))"),
    ("existential", "fol", "∃x (Dog(x) ∧ Black(x))", "∃x (Dog(x) ∧ Black(x))"),
    ("counting", "fol", "∃≥40 x Carbon(x)", "∃≥40 x Carbon(x)"),
    ("counting-exact", "fol", "∃=2 x Ring(x)", "∃=2 x Ring(x)"),
    ("sorted-quantifier", "msfol", "∀x:Person Mortal(x)", "∀x:Person Mortal(x)"),
    ("tptp-annotated", "tptp", "fof(a1, axiom, ![X]: (p(X) => q(X))).",
     "∀x (P(x) → Q(x))"),
    ("tptp-bare", "tptp_bare", "![X]: (p(X) => q(X))", "∀x (P(x) → Q(x))"),
    ("tptp-lowercase-predicates", "tptp_bare", "c(A1) & o(A2) & bDOUBLE(A1,A2)",
     "C(a1) ∧ O(a2) ∧ BDOUBLE(a1, a2)"),
    ("tptp-quoted-name", "tptp_bare", "'1,2-diacyl-sn-glycero-3-phosphocholine'",
     "1,2-diacyl-sn-glycero-3-phosphocholine"),
    ("tptp-biimplication-precedence", "tptp_bare", "p <=> a & b", "P ↔ A ∧ B"),
    ("latex", "latex", r"\forall x (P(x) \rightarrow Q(x))", "∀x (P(x) → Q(x))"),
    ("prover9", "prover9", "all X (P(X) -> Q(X))", "∀x (P(x) → Q(x))"),
    ("modal", "modal", "□(P → ◇Q)", "□(P → ◇Q)"),
)


def _examples(*labels: str) -> List[dict]:
    by_label = {label: (dialect, text, rendering)
                for label, dialect, text, rendering in EXAMPLES}
    out = []
    for label in labels:
        dialect, text, rendering = by_label[label]
        out.append({"label": label, "dialect": dialect, "input": text,
                    "renders_as": rendering})
    return out


def _overview() -> dict:
    from ..fol.dialect_detect import DIALECT_SIGNALS
    from ..api import _UNICODE_MODES

    return {
        "summary": (
            "Formulas are passed as plain text. The dialect is auto-detected "
            "unless you pass an explicit hint; detection nominates candidates "
            "in a fixed order and always falls back to the kit's own unicode "
            "surface syntax."),
        "dialects_in_detection_order": (
            [name for name, _signal, _ascii in DIALECT_SIGNALS] + ["unicode"]),
        "unicode_modes": [name for name, _kwargs in _UNICODE_MODES],
        "most_common_mistake": (
            "Assuming a lowercase name is a predicate. In the kit's OWN "
            "unicode syntax a single lowercase letter is a VARIABLE and a "
            "predicate must start uppercase — see topic 'naming'. In TPTP the "
            "convention is exactly inverted. If your vocabulary has lowercase "
            "predicate names (as chemical signatures do), write TPTP."),
        "topics": list(SPEC_TOPICS),
    }


def _naming() -> dict:
    return {
        "summary": (
            "The kit's unicode syntax decides a symbol's KIND from its shape, "
            "with no declaration needed. Getting this wrong is the single "
            "most common cause of a formula that parses into something other "
            "than what was meant, or fails to parse at all."),
        "rules": [
            {"kind": "variable", "shape": "one lowercase letter, optional digits",
             "matches": ["x", "y", "a", "x1", "a1"],
             "note": "'a1' is a VARIABLE, not a constant — digits do not "
                     "change the kind."},
            {"kind": "constant", "shape": "lowercase word, at least two letters",
             "matches": ["alice", "rex", "socrates"],
             "note": "Use a multi-letter name whenever you mean a specific "
                     "individual; 'a' would be read as a variable."},
            {"kind": "predicate", "shape": "starts with an UPPERCASE letter",
             "matches": ["P", "Dog", "PRED", "HasBond"],
             "note": "'p(x)' does NOT parse as a predicate application in the "
                     "unicode dialect."},
            {"kind": "function", "shape": "lowercase name applied to arguments",
             "matches": ["f(x)", "mother(alice)"],
             "note": "A lowercase name followed by '(' is a function term; the "
                     "same name standing alone is a variable or constant."},
        ],
        "tptp_convention_is_inverted": (
            "In TPTP, lowercase is a predicate/function and UPPERCASE is a "
            "variable: 'p(X)' means predicate p applied to variable X. On "
            "import the kit normalises to its own convention, so TPTP 'c(A1)' "
            "becomes 'C(a1)'. This is a faithful, injective renaming — but "
            "expect the case to flip when you read a formula back."),
        "examples": _examples("variable-vs-constant", "function-term",
                              "equality", "tptp-lowercase-predicates"),
    }


def _dialects() -> dict:
    from ..fol.dialect_detect import DIALECT_SIGNALS

    notes = {
        "smtlib": "SMT-LIB 2 assertions; multiple asserts fold into their "
                  "conjunction.",
        "tptp": "Annotated TPTP (fof/cnf/tff/thf). parse_formula handles ONE "
                "formula; use a problem loader for whole files.",
        "latex": "LaTeX math macros (\\forall, \\land, \\rightarrow, ...).",
        "tptp_bare": "A bare TPTP formula without the fof(...) wrapper. "
                     "Nominated only for pure-ASCII input.",
        "prover9": "Prover9/LADR syntax (all/exists, ->, <->, &, |). "
                   "Nominated only for pure-ASCII input.",
        "unicode": "The kit's own surface syntax — the fallback, and the only "
                   "one covering every logic family the kit supports.",
    }
    return {
        "summary": (
            "Detection is signal-based and ordered; each candidate is tried "
            "and a parse failure falls through to the next, so a wrong guess "
            "costs nothing but the fallback is always the unicode ladder."),
        "dialects": [
            {"name": name, "ascii_only": ascii_only,
             "signal_regex": signal.pattern, "note": notes.get(name, "")}
            for name, signal, ascii_only in DIALECT_SIGNALS
        ] + [{"name": "unicode", "ascii_only": False, "signal_regex": None,
              "note": notes["unicode"]}],
        "how_to_pin": (
            "Pass dialect=<name> to any tool to skip detection. Use this "
            "whenever you generate in a fixed target syntax — it turns a "
            "silent mis-detection into an explicit parse error."),
        "examples": _examples("tptp-annotated", "tptp-bare", "latex",
                              "prover9"),
    }


def _operators() -> dict:
    return {
        "summary": (
            "Precedence, loosest binding LAST. Unary negation binds tightest; "
            "the biconditional loosest. Implication is right-associative. "
            "READ 'unicode_grammar_is_stricter' BELOW before relying on the "
            "numeric levels: they describe the ASCII dialects (TPTP, LaTeX, "
            "Prover9); the kit's own unicode syntax refuses some of these "
            "combinations outright instead of resolving them."),
        "unicode_grammar_is_stricter": (
            "In the kit's OWN unicode syntax, ∧, ∨ and ⊕ sit at ONE level and "
            "may not be mixed without brackets: 'A ∧ B ∨ C' is a SYNTAX "
            "ERROR, not a formula with a default precedence. A chain of the same "
            "connective is fine ('A ∧ B ∧ C'), and the levels relative to → "
            "and ↔ do apply ('A ∧ B → C' parses as '(A ∧ B) → C'). In TPTP "
            "the same input resolves by precedence ('a & b | c' is "
            "'(a & b) | c'). Bracket explicitly and the two agree."),
        "table": [
            {"operator": "negation", "unicode": "¬", "tptp": "~",
             "latex": "\\lnot", "prover9": "-", "binds": "tightest"},
            {"operator": "conjunction", "unicode": "∧", "tptp": "&",
             "latex": "\\land", "prover9": "&",
             "binds": "2 (ASCII dialects); one level with ∨/⊕ in unicode"},
            {"operator": "disjunction", "unicode": "∨", "tptp": "|",
             "latex": "\\lor", "prover9": "|",
             "binds": "3 (ASCII dialects); one level with ∧/⊕ in unicode"},
            {"operator": "exclusive or", "unicode": "⊕", "tptp": "<~>",
             "latex": "\\oplus", "prover9": None,
             "binds": "3 (ASCII dialects); one level with ∧/∨ in unicode"},
            {"operator": "implication", "unicode": "→", "tptp": "=>",
             "latex": "\\rightarrow", "prover9": "->",
             "binds": "4, right-associative"},
            {"operator": "biconditional", "unicode": "↔", "tptp": "<=>",
             "latex": "\\leftrightarrow", "prover9": "<->", "binds": "loosest"},
        ],
        "bracketing_advice": (
            "'p <=> a & b' means 'p <=> (a & b)' — conjunction binds tighter "
            "than the biconditional, and this kit's parser reads it that way. "
            "Write the brackets anyway: some other TPTP tools reject the "
            "unbracketed form, and explicit brackets are never wrong."),
        "examples": _examples("tptp-biimplication-precedence"),
    }


def _quantifiers() -> dict:
    return {
        "summary": (
            "A quantifier binds ONE variable and scopes over the following "
            "prefix-level expression: an atom, a negation, another "
            "quantifier, or a PARENTHESISED formula. To scope over a "
            "connective, parenthesise it."),
        "forms": [
            {"meaning": "for all", "unicode": "∀x φ", "tptp": "![X]: φ",
             "latex": "\\forall x\\, φ", "prover9": "all X φ"},
            {"meaning": "there is", "unicode": "∃x φ", "tptp": "?[X]: φ",
             "latex": "\\exists x\\, φ", "prover9": "exists X φ"},
            {"meaning": "sorted (many-sorted mode only)",
             "unicode": "∀x:Person φ", "tptp": None, "latex": None,
             "prover9": None,
             "note": "Requires the msfol dialect; plain 'fol' rejects the "
                     "':Sort' annotation."},
        ],
        "scope_pitfall": (
            "'∀x P(x) → Q(x)' parses as '(∀x P(x)) → Q(x)' with a FREE x in "
            "Q(x). Write '∀x (P(x) → Q(x))'. A free variable is reported by "
            "the check tool — treat that report as a scoping bug, not a "
            "cosmetic warning."),
        "examples": _examples("universal", "existential", "sorted-quantifier"),
    }


def _counting() -> dict:
    return {
        "summary": (
            "The counting quantifier states a cardinality directly: '∃≥n x φ' "
            "is true iff at least n DISTINCT individuals satisfy φ ('∃≤n' at "
            "most, '∃=n' exactly). The bound stays symbolic, so a large n "
            "costs nothing to write down."),
        "forms": [
            {"meaning": "at least n", "unicode": "∃≥n x φ"},
            {"meaning": "at most n", "unicode": "∃≤n x φ"},
            {"meaning": "exactly n", "unicode": "∃=n x φ"},
        ],
        "why_not_an_existential_chain": (
            "Writing 'at least 40 carbons' as 40 nested existentials plus all "
            "pairwise inequalities means 780 inequality literals for n=40 — a "
            "documented cause of model-checking timeouts, and the model "
            "checker treats separately introduced variables as distinct "
            "anyway. '∃≥40 x Carbon(x)' is one node and is counted directly. "
            "Prefer the counting quantifier for every threshold statement."),
        "lowering": (
            "For backends without native counting the kit expands to the "
            "standard distinct-witnesses encoding automatically — you never "
            "need to write that expansion by hand."),
        "examples": _examples("counting", "counting-exact"),
    }


def _chemistry() -> dict:
    return {
        "summary": (
            "A molecule is a finite first-order structure: the non-hydrogen "
            "atoms are the domain, atom properties are unary predicates, "
            "bonds are binary predicates, and whole-molecule properties are "
            "0-ary. A class definition is a sentence checked against that "
            "structure."),
        "critical_dialect_note": (
            "This vocabulary uses LOWERCASE predicate names (c, o, n, s). In "
            "the kit's unicode syntax those are variables/functions, so "
            "chemical definitions MUST be written in TPTP, where lowercase is "
            "a predicate. Pin it with dialect='tptp_bare' rather than relying "
            "on detection."),
        "signature": {
            "atom_types": ["c", "o", "n", "s", "p", "h"],
            "hydrogen_count": ["has_0_hs", "has_1_hs", "has_2_hs", "has_3_hs"],
            "charge": ["charge0", "charge_m1", "charge_p1"],
            "bonds_binary": ["bSINGLE", "bDOUBLE", "bTRIPLE", "bAROMATIC",
                             "bond", "has_bond_to"],
            "molecule_global_nullary": ["net_charge_neutral",
                                        "NetChargePositive",
                                        "NetChargeNegative"],
            "note": "Bond relations are stored SYMMETRICALLY (both "
                    "directions), so bSINGLE(a,b) implies bSINGLE(b,a) is "
                    "present as a separate pair — do not add symmetry axioms.",
        },
        "computed_predicates": (
            "Ring membership, aromaticity and connectivity need transitive "
            "closure and are therefore NOT first-order definable over this "
            "signature. They are supplied as COMPUTED predicates on the "
            "structure (in_ring, aromatic, same_fragment) and may be used "
            "freely in a definition — the structure decides them "
            "algorithmically."),
        "class_definition_shape": (
            "A class is defined as a 0-ary predicate equivalence: "
            "'className <=> (superClass & ?[A1,A2]: (...))'. Do NOT give the "
            "defined predicate an argument — 'className(X) <=> ...' leaves X "
            "unbound on the right and is a documented failure mode."),
        "examples": _examples("tptp-lowercase-predicates", "tptp-quoted-name"),
    }


def _errors() -> dict:
    return {
        "summary": (
            "The failure modes observed in LLM-generated chemical FOL, with "
            "the fix for each. The first three are measured failure classes "
            "from a published evaluation, not hypotheticals."),
        "classes": [
            {"kind": "biimplication_bracketing",
             "symptom": "'predicate(x) <=> condition1 & condition2' rejected "
                        "by some TPTP parsers.",
             "fix": "Bracket the right-hand side: '<=> (condition1 & "
                    "condition2)'. This kit's parser accepts both and reads "
                    "them identically, and the repair tool can rewrite the "
                    "text for you.",
             "topic": "operators"},
            {"kind": "mixed_same_level_connectives",
             "symptom": "'A ∧ B ∨ C' rejected with \"Unexpected character "
                        "'∨' … Hint: Cannot mix …\". The message names the "
                        "token in front of the connective, so it can read "
                        "like a complaint about that name — it is not.",
             "fix": "Bracket the intended grouping: '(A ∧ B) ∨ C' or "
                    "'A ∧ (B ∨ C)'. The kit's unicode grammar puts ∧, ∨ and "
                    "⊕ on ONE level and refuses to guess between the two "
                    "readings; renaming anything will fail in the same place. "
                    "The ASCII/TPTP dialects do apply a precedence, which is "
                    "why the same input is accepted there.",
             "topic": "operators"},
            {"kind": "invalid_predicate_name",
             "symptom": "A chemical name used as a predicate starts with a "
                        "digit or contains punctuation, e.g. '(2S)Flavan4One' "
                        "or '1,2-diacyl-sn-glycero-3-phosphocholine'.",
             "fix": "Wrap it in single quotes — TPTP allows any characters "
                    "inside a quoted atomic word. Do NOT invent a sanitised "
                    "camel-case name: that silently discards chemically "
                    "meaningful prefixes and breaks the link to the ontology "
                    "class.",
             "topic": "naming"},
            {"kind": "unbound_variable",
             "symptom": "'threeOxoSteroid(X) <=> (steroid & ?[A1]: c(A1))' — "
                        "X appears on the left but is never bound on the "
                        "right.",
             "fix": "A class definition is 0-ary: drop the argument, "
                    "'threeOxoSteroid <=> (...)'. Never 'fix' it by adding a "
                    "quantifier without knowing what was meant — that changes "
                    "the claim.",
             "topic": "chemistry"},
            {"kind": "redundant_inequalities",
             "symptom": "Dozens of existential variables plus every pairwise "
                        "'!=' between them.",
             "fix": "Use the counting quantifier. Separately introduced "
                    "existential variables are already treated as distinct "
                    "under the all_different convention, so the inequalities "
                    "are pure cost.",
             "topic": "counting"},
            {"kind": "over_general_definition",
             "symptom": "The definition matches far more molecules than the "
                        "class has members (high recall, very low precision).",
             "fix": "Check whether a tiny structure already satisfies it — a "
                    "definition of a 50-atom class satisfied by a 3-atom "
                    "model is under-constrained. Add the constraints that "
                    "distinguish the class from its superclass, not just the "
                    "ones it shares with it.",
             "topic": "chemistry"},
        ],
    }


_TOPIC_BUILDERS = {
    "overview": _overview, "naming": _naming, "dialects": _dialects,
    "operators": _operators, "quantifiers": _quantifiers,
    "counting": _counting, "chemistry": _chemistry, "errors": _errors,
}


def syntax_spec(topic: str = "overview",
                dialect: Optional[str] = None) -> Dict:
    """Return the syntax specification for ``topic``.

    Topics: ``overview`` (dialects and the one mistake everyone makes),
    ``naming`` (what makes a symbol a variable, constant, predicate or
    function — and how TPTP inverts it), ``dialects``, ``operators``
    (precedence table), ``quantifiers`` (scope rules), ``counting`` (the
    cardinality quantifier and why it replaces existential chains),
    ``chemistry`` (molecule-as-structure signature), ``errors`` (measured
    LLM failure modes with fixes). ``dialect`` narrows the examples to one
    dialect where that makes sense.

    Raises:
        ValueError: unknown ``topic`` — the message lists the valid ones.
    """
    if topic not in _TOPIC_BUILDERS:
        raise ValueError(
            f"syntax_spec: unknown topic {topic!r} (one of "
            f"{list(SPEC_TOPICS)})")
    spec = dict(_TOPIC_BUILDERS[topic]())
    spec["topic"] = topic
    if dialect is not None and "examples" in spec:
        spec["examples"] = [e for e in spec["examples"]
                            if e["dialect"] == dialect]
        spec["filtered_to_dialect"] = dialect
    return spec
