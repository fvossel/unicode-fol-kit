"""Command-line interface for unicode-fol-kit.

Parse a Unicode first-order / many-sorted / Łukasiewicz formula and render it
in one of several output formats. Run as::

    python -m unicode_fol_kit "∀x P(x)" --to latex

The ``--mode`` flag selects the parser dialect (which maps onto the
``many_sorted``/``fuzzy`` flags of :class:`MSFLParser`); ``--to`` selects the
rendering applied to the parsed AST.
"""

import argparse
import json
import sys

from .fol.msflparser import MSFLParser
from .fol.naming import NamingError, ParsingError


# Map each --mode value to the (many_sorted, fuzzy) flags of MSFLParser.
_MODE_FLAGS = {
    "fol":   (False, False),
    "msfol": (True, False),
    "msfl":  (True, True),
    "fl":    (False, True),
}


def _render(node, fmt: str) -> str:
    """Render a parsed AST node in the requested output format.

    The mapping mirrors the rendering methods defined on the Node base class;
    ``json`` serialises ``to_dict()`` via :func:`json.dumps`.
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
        return json.dumps(node.to_dict())
    if fmt == "dot":
        return node.to_dot()
    # argparse restricts choices, so this is unreachable in normal use.
    raise ValueError(f"Unknown output format: {fmt}")


def _build_parser() -> argparse.ArgumentParser:
    """Construct the argparse parser for the CLI."""
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
        choices=["fol", "msfol", "msfl", "fl"],
        default="fol",
        help="parser dialect: fol (default), msfol, msfl, or fl",
    )
    parser.add_argument(
        "--to",
        dest="to",
        choices=["tree", "unicode", "latex", "tptp", "prover9", "json", "dot"],
        default="tree",
        help="output rendering (default: tree)",
    )
    return parser


def main(argv=None) -> int:
    """Run the CLI.

    Parses ``argv`` (defaults to ``sys.argv[1:]``), parses the supplied formula
    in the chosen mode, renders it in the chosen format, and prints the result
    to stdout. Returns 0 on success. On a NamingError or ParsingError, prints
    the error message to stderr and returns 1.
    """
    parser = _build_parser()
    args = parser.parse_args(argv)

    many_sorted, fuzzy = _MODE_FLAGS[args.mode]
    formula_parser = MSFLParser(many_sorted=many_sorted, fuzzy=fuzzy)

    try:
        ast = formula_parser.parse(args.formula)
    except (NamingError, ParsingError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    print(_render(ast, args.to))
    return 0


if __name__ == "__main__":
    sys.exit(main())
