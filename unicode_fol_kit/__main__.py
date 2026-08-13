"""Command-line interface for unicode-fol-kit.

Two ways to run this module, dispatched purely on ``argv[0]``:

**Legacy mode** (unchanged since Tier 0) — parse a single formula and render
it in one output format::

    python -m unicode_fol_kit "∀x P(x)" --to latex

The ``--mode`` flag selects the parser dialect (which maps onto the
constructor flags of :class:`MSFLParser`, table-driven via ``_MODE_KWARGS``);
``--to`` selects the rendering applied to the parsed AST.

**Subcommand mode** — a 1:1 mirror of :mod:`unicode_fol_kit.api`'s verbs onto
the command line, for every ``argv[0]`` in
``{check, equiv, prove, countermodel, repair, translate}``::

    python -m unicode_fol_kit check "∀x P(x)"
    python -m unicode_fol_kit equiv "P → Q" "¬P ∨ Q"
    python -m unicode_fol_kit prove "Q" --premise "P" --premise "P → Q"
    python -m unicode_fol_kit countermodel "∀x P(x)"
    python -m unicode_fol_kit repair "∀x (P(x)"
    python -m unicode_fol_kit translate "□P" --from modal --to-logic fol

Dispatch rule: if ``argv`` is non-empty and ``argv[0]`` names one of the six
subcommands above, the rest of ``argv`` is parsed by that subcommand's own
parser; otherwise ``argv`` goes to the legacy single-formula parser
unchanged. Because the legacy grammar's first positional is the formula
itself, a formula that happens to be spelled exactly ``"check"`` (etc.) would
be misrouted — an acceptable, documented edge case shared with any CLI that
grows subcommands after a positional-argument v1.

Every subcommand accepts three common flags: ``--dialect`` (the
:func:`~unicode_fol_kit.api.parse_any` dialect hint; omitted means
auto-detect), ``--json`` (machine-readable ``to_dict()`` JSON instead of the
default human-readable summary), and ``--timeout`` (milliseconds, forwarded
to whichever backend/solver call the subcommand makes; accepted uniformly
even by subcommands with nothing to forward it to).

Error culture: a malformed FORMULA argument to ``check``/``repair`` is not an
error — that is the diagnosis those two verbs exist to report (``ok=False``,
exit 1). For every other subcommand, a formula that :func:`api.parse_any`
cannot parse, an unknown/unavailable backend
(:class:`~unicode_fol_kit.atp.protocol.BackendUnavailable`), an unsupported
translation fragment (``NotImplementedError``), or a bad ``--signature``
JSON file all print one clean message to stderr and exit 3 — never a Python
traceback.
"""

import argparse
import json
import sys

from .fol.msflparser import MSFLParser
from .fol.naming import NamingError, ParsingError
from . import api
from .atp.protocol import BackendUnavailable


# Map each --mode value to the MSFLParser constructor kwargs it selects. Every
# entry here must be a legal (non-conflicting) combination on its own — see
# MSFLParser's own mutual-exclusivity rules (module docstring / __init__).
# Reused (read-only) by the subcommand dispatcher below: its keys double as
# the set of dialect-hint names that :func:`~unicode_fol_kit.api.parse_any`
# also accepts verbatim (see ``_dialect_hint_for_source``).
_MODE_KWARGS = {
    "fol":          {},
    "msfol":        {"many_sorted": True},
    "msfl":         {"many_sorted": True, "fuzzy": True},
    "fl":           {"fuzzy": True},
    "modal":        {"modal": True},
    "second_order": {"second_order": True},
    "dependence":   {"dependence": True},
    "linear":       {"linear": True},
    "lambek":       {"lambek": True},
}


def _render(node, fmt: str) -> str:
    """Render a parsed AST node in the requested output format.

    The mapping mirrors the rendering methods defined on the Node base class;
    ``json`` emits the versioned envelope of
    :func:`unicode_fol_kit.fol.serialize.serialize` (``schema_version`` + the
    ``to_dict()`` tree under ``root``) via :func:`json.dumps`.
    """
    if fmt == "tree":
        return node.tree_str()
    if fmt == "unicode":
        return node.to_unicode_str()
    if fmt == "latex":
        return node.to_latex()
    if fmt == "tptp":
        return node.to_tptp()
    if fmt == "prover9":
        return node.to_prover9()
    if fmt == "json":
        from .fol.serialize import serialize
        return json.dumps(serialize(node))
    if fmt == "dot":
        return node.to_dot()
    # argparse restricts choices, so this is unreachable in normal use.
    raise ValueError(f"Unknown output format: {fmt}")


def _build_parser() -> argparse.ArgumentParser:
    """Construct the argparse parser for the legacy single-formula CLI."""
    parser = argparse.ArgumentParser(
        prog="unicode_fol_kit",
        description="Parse and render a Unicode first-order logic formula.",
    )
    parser.add_argument(
        "formula",
        metavar="FORMULA",
        help="the formula string to parse (e.g. \"∀x P(x)\")",
    )
    parser.add_argument(
        "--mode",
        choices=sorted(_MODE_KWARGS),
        default="fol",
        help=(
            "parser dialect: fol (default), msfol, msfl, fl, modal, "
            "second_order, dependence, linear, or lambek"
        ),
    )
    parser.add_argument(
        "--to",
        dest="to",
        choices=["tree", "unicode", "latex", "tptp", "prover9", "json", "dot"],
        default="tree",
        help="output rendering (default: tree)",
    )
    return parser


def _run_legacy(argv) -> int:
    """The original (Tier 0) single-formula parse-and-render behaviour."""
    parser = _build_parser()
    args = parser.parse_args(argv)

    formula_parser = MSFLParser(**_MODE_KWARGS[args.mode])

    try:
        ast = formula_parser.parse(args.formula)
    except (NamingError, ParsingError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    print(_render(ast, args.to))
    return 0


# ---------------------------------------------------------------------------
# Subcommands: a 1:1 mirror of unicode_fol_kit.api onto the command line.
# ---------------------------------------------------------------------------

_SUBCOMMANDS = ("check", "equiv", "prove", "countermodel", "repair", "translate")

# api.translate's logic labels that do not coincide with a parse_any dialect
# hint of the same name (see _dialect_hint_for_source).
_LOGIC_TO_DIALECT_HINT = {"team": "dependence"}


def _add_common(parser: argparse.ArgumentParser) -> None:
    """Add the three flags shared by every subcommand (see module docstring)."""
    parser.add_argument(
        "--dialect", default=None, metavar="DIALECT",
        help="parse_any dialect hint (default: auto-detect)")
    parser.add_argument(
        "--json", dest="as_json", action="store_true",
        help="machine-readable JSON output (default: human-readable summary)")
    parser.add_argument(
        "--timeout", type=int, default=10000, metavar="MS",
        help="backend/solver timeout in milliseconds (default: 10000)")


def _parse_or_raise(text: str, dialect):
    """Parse ``text`` via :func:`api.parse_any`, raising ``ValueError`` on failure.

    Used by every subcommand that needs an actual :class:`Node` to hand to a
    decision API (``equiv``/``prove``/``countermodel``/``translate``) —
    unlike ``check``/``repair``, which treat a parse failure as their own
    diagnosis rather than a hard error (see module docstring).
    """
    result = api.parse_any(text, hint=dialect)
    if not result.ok:
        message = (result.errors[-1]["message"] if result.errors
                   else f"no parser accepted {text!r}")
        raise ValueError(f"could not parse {text!r}: {message}")
    return result.formula


def _load_json_file(path: str) -> dict:
    """Load a JSON object from ``path`` (used for ``--signature`` files)."""
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def _print_kv(pairs) -> None:
    """Print ``key: value`` lines — the shared shape of every human summary."""
    for key, value in pairs:
        print(f"{key}: {value}")


# -- check -------------------------------------------------------------- #

def _cmd_check(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="unicode_fol_kit check",
        description="Well-formedness report for a formula, optionally against a signature.")
    parser.add_argument("formula", metavar="FORMULA")
    parser.add_argument(
        "--signature", default=None, metavar="SIG_JSON",
        help="path to a JSON signature spec (see api.check / api._signature_errors)")
    _add_common(parser)
    args = parser.parse_args(argv)

    signature = _load_json_file(args.signature) if args.signature else None
    result = api.check(args.formula, signature=signature, dialect=args.dialect)

    if args.as_json:
        print(json.dumps(result.to_dict()))
    else:
        _print_kv([
            ("ok", result.ok),
            ("parseable", result.parseable),
            ("is_closed", result.is_closed),
            ("arity_consistent", result.arity_consistent),
            ("has_lambdas", result.has_lambdas),
        ])
        if result.free_variables:
            print("free_variables: " + ", ".join(result.free_variables))
        if result.arity_conflicts:
            print("arity_conflicts: " + json.dumps(list(result.arity_conflicts)))
        if result.signature_errors:
            print("signature_errors: " + json.dumps(list(result.signature_errors)))
        if result.error:
            print(f"error: {result.error}")

    return 0 if result.ok else 1


# -- equiv -------------------------------------------------------------- #

def _cmd_equiv(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="unicode_fol_kit equiv",
        description="Graded equivalence between two formulas (api.equivalent).")
    parser.add_argument("formula1", metavar="FORMULA1")
    parser.add_argument("formula2", metavar="FORMULA2")
    parser.add_argument(
        "--method", choices=["exact", "canonical", "predicate_align", "solver", "auto"],
        default="auto", help="equivalence level (default: auto, cheapest-first ladder)")
    _add_common(parser)
    args = parser.parse_args(argv)

    f1 = _parse_or_raise(args.formula1, args.dialect)
    f2 = _parse_or_raise(args.formula2, args.dialect)

    result = api.equivalent(f1, f2, method=args.method, timeout=args.timeout)

    if args.as_json:
        print(json.dumps(result.to_dict()))
    else:
        _print_kv([("equivalent", result.equivalent), ("method_used", result.method_used)])
        if result.counterexample is not None:
            print("counterexample: " + json.dumps(result.counterexample))

    if result.equivalent is True:
        return 0
    if result.equivalent is False:
        return 1
    return 2


# -- prove -------------------------------------------------------------- #

def _cmd_prove(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="unicode_fol_kit prove",
        description="Decide premises |= formula over a chain of backends (api.prove).")
    parser.add_argument("formula", metavar="FORMULA")
    parser.add_argument(
        "--premise", action="append", default=[], metavar="P",
        help="a premise formula (repeatable)")
    parser.add_argument(
        "--backends", default=None, metavar="a,b,c",
        help="comma-separated backend names (default: the logic's default chain)")
    parser.add_argument(
        "--logic", default="auto", metavar="LOGIC",
        help="'auto' (default, routes on modal operators), 'fol', or 'modal'")
    _add_common(parser)
    args = parser.parse_args(argv)

    formula = _parse_or_raise(args.formula, args.dialect)
    premises = [_parse_or_raise(p, args.dialect) for p in args.premise]
    backends = ([b.strip() for b in args.backends.split(",") if b.strip()]
               if args.backends else None)

    verdict = api.prove(formula, premises, logic=args.logic, backends=backends,
                        timeout=args.timeout)

    if args.as_json:
        print(json.dumps(verdict.to_dict()))
    else:
        _print_kv([
            ("status", verdict.status),
            ("backend", verdict.backend),
            ("logic", verdict.logic),
            ("szs", verdict.szs_status),
            ("wall_time", verdict.wall_time),
        ])
        if verdict.reason:
            print(f"reason: {verdict.reason}")
        if verdict.detail:
            print(f"detail: {verdict.detail}")

    return {"proved": 0, "refuted": 1, "unknown": 2, "error": 3}[verdict.status]


# -- countermodel --------------------------------------------------------- #

def _cmd_countermodel(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="unicode_fol_kit countermodel",
        description="Search for a countermodel to premises |= formula (api.countermodel).")
    parser.add_argument("formula", metavar="FORMULA")
    parser.add_argument(
        "--premise", action="append", default=[], metavar="P",
        help="a premise formula (repeatable)")
    _add_common(parser)
    args = parser.parse_args(argv)

    formula = _parse_or_raise(args.formula, args.dialect)
    premises = [_parse_or_raise(p, args.dialect) for p in args.premise]

    result = api.countermodel(formula, premises, timeout=args.timeout)

    if args.as_json:
        print(json.dumps(result.to_dict()))
    else:
        _print_kv([("found", result.found), ("backend", result.backend)])
        if result.explanation_nl:
            print(f"explanation: {result.explanation_nl}")
        if result.model is not None:
            print("model: " + json.dumps(result.model))

    return 0 if result.found else 1


# -- repair --------------------------------------------------------------- #

def _cmd_repair(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="unicode_fol_kit repair",
        description="One diagnose round over raw formula text, no fixer (api.repair).")
    parser.add_argument("text", metavar="TEXT")
    parser.add_argument(
        "--signature", default=None, metavar="SIG_JSON",
        help="path to a JSON signature spec (see api.check / api._signature_errors)")
    _add_common(parser)
    args = parser.parse_args(argv)

    signature = _load_json_file(args.signature) if args.signature else None
    step = next(api.repair(args.text, dialect=args.dialect, signature=signature,
                           fixer=None, max_attempts=1))

    if args.as_json:
        print(json.dumps(step.to_dict()))
    else:
        _print_kv([("ok", step.ok), ("converged", step.converged)])
        if step.suggestion:
            print(f"suggestion: {step.suggestion}")
        print("diagnostics: " + json.dumps(step.diagnostics))

    return 0 if step.ok else 1


# -- translate -------------------------------------------------------------- #

def _dialect_hint_for_source(from_logic: str, explicit):
    """Resolve the parse_any hint for translate's source term.

    An explicit ``--dialect`` always wins. Otherwise: a ``from_logic`` that
    names one of the kit's own unicode modes IS its own parse_any hint
    (``"modal"``, ``"fol"``, …); ``"team"`` (the comorphism registry's label
    for dependence-logic sentences) maps to the ``"dependence"`` mode, since
    the two use different names for the same surface grammar and, unlike
    ``modal``/``fol``, auto-detection cannot disambiguate a dependence atom
    ``=(x,y)`` from a plain FOL equality atom of the same shape. Any other
    label (``"alc"`` is handled separately before this is called; ``"eso"``
    has no surface syntax of its own) falls back to auto-detection.
    """
    if explicit is not None:
        return explicit
    if from_logic in _MODE_KWARGS:
        return from_logic
    return _LOGIC_TO_DIALECT_HINT.get(from_logic)


def _render_translated(obj) -> str:
    """Render a translation result for the human-readable summary.

    Every default-registry target (``fol``, ``modal``, ``eso``) is a
    :class:`~unicode_fol_kit.fol.nodes.Node` (``to_unicode_str``); ALC
    :class:`~unicode_fol_kit.dl.concepts.Concept` only ever appears as a
    SOURCE in the default registry, but ``to_unicode``/``str`` cover it too
    should a future edge target ``alc``.
    """
    if hasattr(obj, "to_unicode_str"):
        return obj.to_unicode_str()
    if hasattr(obj, "to_unicode"):
        return obj.to_unicode()
    return str(obj)


def _cmd_translate(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="unicode_fol_kit translate",
        description="Translate a term between logics via the comorphism registry (api.translate).")
    parser.add_argument("formula", metavar="FORMULA")
    parser.add_argument(
        "--from", dest="from_logic", required=True, metavar="L1",
        help="source logic label (e.g. 'fol', 'modal', 'alc', 'team')")
    parser.add_argument(
        "--to-logic", dest="to_logic", required=True, metavar="L2",
        help="target logic label (e.g. 'fol', 'modal', 'eso') — NOT --to, "
             "which the legacy parser already owns")
    _add_common(parser)
    args = parser.parse_args(argv)

    if args.from_logic == "alc":
        from .dl.parser import parse_concept
        term = parse_concept(args.formula)
    else:
        dialect = _dialect_hint_for_source(args.from_logic, args.dialect)
        term = _parse_or_raise(args.formula, dialect)

    result = api.translate(term, args.from_logic, args.to_logic)

    if args.as_json:
        print(json.dumps(result.to_dict()))
    else:
        _print_kv([
            ("source", result.source),
            ("target", result.target),
            ("path", " -> ".join(result.path) if result.path else "(identity)"),
            ("lossy", result.lossy),
        ])
        if result.note:
            print(f"note: {result.note}")
        print("result: " + _render_translated(result.result))

    return 0


_SUBCOMMAND_HANDLERS = {
    "check": _cmd_check,
    "equiv": _cmd_equiv,
    "prove": _cmd_prove,
    "countermodel": _cmd_countermodel,
    "repair": _cmd_repair,
    "translate": _cmd_translate,
}


def _run_subcommand(name: str, rest_argv) -> int:
    """Dispatch to one subcommand handler, enforcing the error culture.

    argparse usage errors (missing/unknown flags) still raise ``SystemExit``
    straight through, exactly like the legacy parser — those are the user
    misusing the CLI, not a runtime failure to report cleanly. Everything
    else that a handler can raise on a bad-but-well-formed request (an
    unparseable formula from ``_parse_or_raise``, an unknown/unavailable
    backend, an unsupported translation fragment, a malformed
    ``--signature`` file) is caught here, printed as one clean message, and
    turned into exit code 3.
    """
    handler = _SUBCOMMAND_HANDLERS[name]
    try:
        return handler(rest_argv)
    except (ValueError, BackendUnavailable, NotImplementedError, OSError) as exc:
        print(f"{name}: {exc}", file=sys.stderr)
        return 3


def main(argv=None) -> int:
    """Run the CLI: dispatch to a subcommand, or fall back to the legacy parser.

    Parses ``argv`` (defaults to ``sys.argv[1:]``). If ``argv`` is non-empty
    and ``argv[0]`` is one of ``check``/``equiv``/``prove``/``countermodel``/
    ``repair``/``translate``, the rest of ``argv`` is handed to that
    subcommand; otherwise the whole of ``argv`` goes to the legacy
    single-formula parse-and-render path (see module docstring for both).
    """
    if argv is None:
        argv = sys.argv[1:]
    if argv and argv[0] in _SUBCOMMANDS:
        return _run_subcommand(argv[0], argv[1:])
    return _run_legacy(argv)


if __name__ == "__main__":
    sys.exit(main())
