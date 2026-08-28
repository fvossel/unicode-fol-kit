from .msflparser import MSFLParser
from .nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Count, Measure, Cardinality, Contrast,
    Z3Env,
    node_at, replace_at,
    SortedQuantifier, SortedConstant,
    SortedCount, SortedCardinality,
    Nominal, At,
    Dependence, SlashedExists,
    Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero,
    Product, Under, Over,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Would, Might,
    Announce, AnnounceDiamond,
    SecondOrderQuantifier,
    PredicateTerm, Signatures, analyse_signatures, MixedSlotError,
    free_variables,
    substitute, beta_reduce, ReductionLimitError,
    eta_reduce, beta_eta_normalize,
    resolve_lambda_scope,
    to_fol,
)
from .normalforms import to_nnf, to_pnf, to_cnf, to_dnf, to_tseitin_cnf, skolemize, is_horn
from .lambda_tools import has_lambdas, eliminate_lambdas, beta_reduce_step, reduce_trace
from .unification import unify, apply_subst
from .modal_translation import standard_translation, hybrid_is_valid
from .pal import reduce_announcements
from .latex_input import latex_to_unicode, parse_latex
from .tptp_input import (
    parse_tptp, parse_tptp_formula, load_tptp, TptpFormula,
    parse_tptp_problem, load_tptp_problem, TptpProblem, TptpHeader,
)
from .prover9_input import (
    parse_prover9, parse_prover9_problem, load_prover9, Prover9Formula,
)
from .prolog_input import (
    parse_prolog_clause, parse_prolog_program, load_prolog, PrologParsingError,
)
from .sanitize import sanitize_names, sanitize_all, NameMapping
from .verbalize import to_english
from .derivation import CCGDerivation, reduction_derivation
from .frames import (
    AXIOM_ALIASES, FRAMES, FRAME_CONDITIONS, MODAL_AXIOMS,
    UnsupportedFrameCondition, resolve_frame, geach_axiom,
    holds_on_finite_frame, modal_axiom, unguarded_frame_axiom,
)
from .qml import (
    qml_translate, qml_axioms, qml_is_valid, qml_equivalent,
    to_thf_modal, to_isabelle_modal, BARCAN, CONVERSE_BARCAN, QML_BRIDGES,
)
from .naming import NamingError, ParsingError
from .spans import (
    Span, UNKNOWN, NodeSpans, Path, SpanMap, SpannedFormula,
    traverse, build_span_map, project_spans,
)
from .serialize import SCHEMA_VERSION, serialize, deserialize
from .casl_export import to_casl_spec, formula_to_casl
from .casl_import import parse_casl_spec, CaslSpec, CaslImportError
from .tptp_repair import (
    repair_tptp_formula, repair_tptp_problem, RepairResult, Issue,
    ProblemRepairEntry, ProblemRepairResult, TptpRepairError,
)
from .dialect_repair import repair_formula, DialectRepairResult
from .simplify_check import (
    simplify_for_checking, SimplifyResult,
    count_from_existential_chain, expand_count,
)
from .dialect_detect import detect_dialects
from .signature import (
    Signature, PredicateDecl, FunctionDecl, ConstantDecl,
)

__all__ = [
    # The shared modal frame registry — one table for every modal route.
    "FRAMES", "FRAME_CONDITIONS", "MODAL_AXIOMS", "AXIOM_ALIASES",
    "modal_axiom", "resolve_frame", "geach_axiom",
    "holds_on_finite_frame", "unguarded_frame_axiom",
    "UnsupportedFrameCondition",
    "MSFLParser",
    "Node", "Variable", "Constant", "Number", "Function",
    "Atom", "Not", "And", "Or", "Xor", "Implies", "Iff", "Quantifier",
    "Count", "Measure", "Cardinality", "Contrast",
    "Z3Env",
    "node_at", "replace_at",
    "NamingError", "ParsingError",
    "Span", "UNKNOWN", "NodeSpans", "Path", "SpanMap", "SpannedFormula",
    "traverse", "build_span_map", "project_spans",
    "SCHEMA_VERSION", "serialize", "deserialize",
    "to_casl_spec", "formula_to_casl",
    "parse_casl_spec", "CaslSpec", "CaslImportError",
    "repair_tptp_formula", "repair_tptp_problem", "RepairResult", "Issue",
    "ProblemRepairEntry", "ProblemRepairResult", "TptpRepairError",
    "repair_formula", "DialectRepairResult",
    "parse_prolog_clause", "parse_prolog_program", "load_prolog",
    "PrologParsingError",
    "simplify_for_checking", "SimplifyResult",
    "count_from_existential_chain", "expand_count",
    "detect_dialects",
    "Signature", "PredicateDecl", "FunctionDecl", "ConstantDecl",
    "SortedQuantifier", "SortedConstant",
    "SortedCount", "SortedCardinality",
    "Nominal", "At",
    "Dependence", "SlashedExists",
    "Tensor", "With", "OPlus", "LinearImplies", "OfCourse", "One", "Top", "Zero",
    "Product", "Under", "Over",
    "WeakConjunction", "WeakDisjunction",
    "StrongConjunction", "StrongDisjunction",
    "LukNegation", "LukImplication", "LukEquivalence",
    "LambdaVar", "Lambda", "Application",
    "Box", "Diamond", "Knows", "Believes", "Says", "Wants",
    "Always", "Eventually", "Next", "Until",
    "Historically", "Once", "Previous", "Since",
    "Obligatory", "Permitted",
    "Would", "Might",
    "Announce", "AnnounceDiamond",
    "SecondOrderQuantifier",
    "PredicateTerm", "Signatures", "analyse_signatures", "MixedSlotError",
    "free_variables",
    "substitute", "beta_reduce", "ReductionLimitError",
    "eta_reduce", "beta_eta_normalize",
    "resolve_lambda_scope",
    "to_fol",
    "to_nnf", "to_pnf", "to_cnf", "to_dnf", "to_tseitin_cnf", "skolemize", "is_horn",
    "has_lambdas", "eliminate_lambdas", "beta_reduce_step", "reduce_trace",
    "unify", "apply_subst",
    "standard_translation", "hybrid_is_valid",
    "reduce_announcements",
    "latex_to_unicode", "parse_latex",
    "parse_tptp", "parse_tptp_formula", "load_tptp", "TptpFormula",
    "parse_tptp_problem", "load_tptp_problem", "TptpProblem", "TptpHeader",
    "parse_prover9", "parse_prover9_problem", "load_prover9", "Prover9Formula",
    "sanitize_names", "sanitize_all", "NameMapping",
    "to_english",
    "CCGDerivation", "reduction_derivation",
    "qml_translate", "qml_axioms", "qml_is_valid", "qml_equivalent",
    "to_thf_modal", "to_isabelle_modal", "BARCAN", "CONVERSE_BARCAN",
    "QML_BRIDGES",
]
