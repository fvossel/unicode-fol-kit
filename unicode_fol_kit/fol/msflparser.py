"""MSFLParser: unified parser for FOL, MSFOL, and MSFL modes."""

import pathlib
from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from lark.exceptions import VisitError

from .nodes import Node, FOLTransformer
from ._msfl_nodes import LambdaVar, Lambda, Application, resolve_lambda_scope
from ._fol_nodes import (
    Variable, Constant, Function,
    build_grammar, build_transform_handlers, PARSER_OPS,
)
from ._modal_nodes import resolve_agent_variables
from ._so_nodes import ConflictingArityError  # re-exported for callers/tests
from .naming import NamingError, ParsingError

_GRAMMARS_DIR = pathlib.Path(__file__).parent / "grammars"


# =========================
# Single-letter function-call patch
# =========================
#
# The shared (non-registry) term layer in _fol_nodes.py's grammar template only
# ever lets a NAME (>= 2 letters) head a function call: ``NAME "(" termlist
# ")" -> function_``. A single lowercase letter lexes as VARIABLE instead of
# NAME, and ``?atom_term: VARIABLE`` has no continuation into "(", so
# ``f(x)`` fails at the LEXER level (a NamingError: '(' is not a valid
# continuation after VARIABLE in that grammar position) even though
# ``Function('f', [...])`` is a perfectly legal AST node — e.g.
# ``Function('f', [...]).to_unicode_str()`` prints ``f(x)``, which then FAILS
# to re-parse. Verified unambiguous (no Earley ambiguity against lambda
# application or the atom/atom_term rules: VARIABLE-as-bare-term and
# VARIABLE-as-function-head are distinguished purely by whether "(" follows,
# and a bare term can never itself reduce to a formula, so there is no
# competing derivation for e.g. "(f)(y)" or "(λx. P(x))(f(y))") by building the
# patched grammar for every mode and cross-checking against an
# ``ambiguity="explicit"`` Earley parser, plus running the full parser test
# suite (test_msfl_parser.py, test_lambda_tools.py, test_resolve_lambda_scope.py).
#
# The fix belongs at the shared-template level (_fol_nodes.py's
# _BASE_GRAMMAR_TEMPLATE), but that module is out of scope for this change,
# so it is applied here as a targeted, self-checking patch to the ASSEMBLED
# grammar string: splice in a ``VARIABLE "(" termlist ")" -> function_``
# alternative right next to the existing bare-VARIABLE one. The patch is
# applied identically to every mode, since the term layer is verbatim-shared
# across all of them (build_grammar's per-mode variation is entirely in the
# formula-operator layers, not atom_term).
_ATOM_TERM_VARIABLE_MARKER = '?atom_term: VARIABLE\n'
_ATOM_TERM_FUNCTION_PATCH = (
    _ATOM_TERM_VARIABLE_MARKER
    + '    | VARIABLE "(" termlist ")"          -> function_\n'
)


def _allow_single_letter_function_calls(grammar_text: str) -> str:
    """Splice a VARIABLE-headed function-call alternative into atom_term.

    Returns ``grammar_text`` with exactly one occurrence of the bare
    ``?atom_term: VARIABLE`` line followed by a new
    ``VARIABLE "(" termlist ")" -> function_`` alternative (same rule alias as
    the existing NAME-headed case, so no new Transformer method name is
    needed — only ``function_`` itself is extended, see
    :meth:`LambdaTransformer.function_`).

    Raises RuntimeError if the marker is not found exactly once: a template
    change in ``_fol_nodes.py`` would otherwise make this patch silently a
    no-op and quietly resurrect the single-letter-function bug.
    """
    count = grammar_text.count(_ATOM_TERM_VARIABLE_MARKER)
    if count != 1:
        raise RuntimeError(
            "MSFLParser: expected exactly one '?atom_term: VARIABLE' line in "
            f"the generated grammar, found {count}. The shared term layer in "
            "_fol_nodes.py's grammar template has changed shape; update "
            "_allow_single_letter_function_calls (msflparser.py) to match, or "
            "the single-letter function-call fix silently stops applying."
        )
    return grammar_text.replace(
        _ATOM_TERM_VARIABLE_MARKER, _ATOM_TERM_FUNCTION_PATCH, 1)


class LambdaTransformer(FOLTransformer):
    """Extends FOLTransformer with lambda-abstraction and application handlers.

    All three parser modes inherit these via the class hierarchy, so λ-syntax
    is available in FOL, MSFOL, and MSFL without duplicating the handlers.

    Lambda/LambdaVar/Application are defined in _msfl_nodes.py (which imports
    from _fol_nodes.py), so this class lives in msflparser.py rather than
    _fol_nodes.py to avoid a circular import.
    """

    def lambda_(self, items):
        # Grammar: LAMBDA (VARIABLE | NAME | PREDICATE) "." formula
        # LAMBDA is a named terminal, so it appears as items[0] (raw Token).
        # "." is a string literal and is filtered out by Lark.
        # items[1] is the parameter, already processed by terminal handlers:
        #   VARIABLE  → Variable node (via FOLTransformer.VARIABLE)
        #   NAME      → Constant node (via FOLTransformer.NAME)
        #   PREDICATE → raw Token     (no terminal handler for PREDICATE)
        # items[2] is the body node.
        param = items[1]
        if isinstance(param, (Variable, Constant)):
            param_name = param.name
        else:
            param_name = str(param)     # raw Token for PREDICATE params, e.g. λP. …
        return Lambda(LambdaVar(param_name), items[2])

    def application_(self, items):
        return Application(items[0], items[1])

    def function_(self, items):
        """Transform a function application into a Function node.

        Extends ``FOLTransformer.function_`` to also accept a single-letter
        VARIABLE head, not just a multi-letter NAME: the
        ``VARIABLE "(" termlist ")" -> function_`` alternative spliced into
        atom_term by :func:`_allow_single_letter_function_calls` reduces to
        this SAME rule alias, so both cases arrive here. Lark transforms
        bottom-up, so by the time this fires the head token has already been
        turned into a node by its terminal handler: a Constant (NAME) or a
        Variable (VARIABLE) — never a raw Token — so both are unwrapped via
        ``.name``.
        """
        head = items[0]
        if isinstance(head, (Constant, Variable)):
            name = head.name
        else:
            name = str(head)
        args = items[1:]
        if args and isinstance(args[0], list):
            args = args[0]
        return Function(name, args)


# The per-mode hand-written transformers (Modal/SecondOrder/MSFOL/MSFL/FL +
# LukConnectivesMixin) and the six per-mode .lark grammars were retired once the
# registry pipeline (build_grammar / build_transform_handlers over PARSER_OPS) was
# verified to reproduce them byte-for-byte. The runtime now assembles every mode from
# the registry on a shared LambdaTransformer base (see _assemble_transformer); only
# terminals.lark survives, imported by the generated grammar.


# MSFLParser's short mode name (used in NamingError/ParsingError messages) -> the
# registry mode key consumed by build_grammar / build_transform_handlers.
_REGISTRY_MODE = {
    "fol": "fol", "msfol": "msfol", "msfl": "msfl", "fl": "fl",
    "modal": "modal", "so": "second_order",
    "dependence": "dependence", "linear": "linear", "lambek": "lambek",
}


# Compiled Lark parsers are cached per (registry_mode, registry size): building
# the Earley grammar is the expensive step, and it depends only on the registered
# ParserOps. Keying on len(PARSER_OPS) rebuilds automatically if an operator is
# registered at runtime (the registry is otherwise frozen after import).
_PARSER_CACHE: dict = {}


def _assemble_transformer(registry_mode: str) -> LambdaTransformer:
    """Build the Transformer for a registry mode from the parser registry.

    The base is a LambdaTransformer, which carries the shared, non-operator
    term/atom/lambda/application handlers (VARIABLE, NAME, function_, atom_, sum,
    product, lambda_, …) common to every mode. The mode's registered operator
    handlers (build_transform_handlers) are then attached as INSTANCE attributes.

    Instance — not class — attributes are essential: a plain ``transform(items)``
    function attached to the instance is returned bare by ``getattr(self, alias)``,
    so Lark calls it with the rule's children as the sole argument. Attached to the
    class it would become a bound method and receive ``self`` as ``items``.
    """
    transformer = LambdaTransformer()
    for alias, fn in build_transform_handlers(registry_mode).items():
        setattr(transformer, alias, fn)
    return transformer


class MSFLParser:
    """Unified parser supporting FOL, MSFOL, MSFL, FL, modal, and second-order modes.

    Args:
        many_sorted: if True, quantifiers and constants must carry sort
            annotations (e.g. ``∀x:Human P(x)``, ``alice:Human``).
        fuzzy: if True, use Łukasiewicz operators (⊗ ⊕ for strong
            conjunction/disjunction; ¬ → ↔ map to Łukasiewicz nodes).
        modal: if True, parse classical unsorted FOL extended with modal,
            epistemic, doxastic, temporal, and deontic operators
            (□ ◇ K_a B_a Ⓖ Ⓕ Ⓝ Ⓤ Ⓞ Ⓟ). Cannot be combined with many_sorted or
            fuzzy in v1.
        second_order: if True, parse classical unsorted FOL extended with
            second-order quantifiers over predicate variables (∀P / ∃P, where P
            is an uppercase PREDICATE; the bound predicate's arity is inferred
            from its applications in the body). Cannot be combined with
            many_sorted, fuzzy, or modal in v1.
        dependence: if True, parse the team-semantic dependence/IF fragment —
            literals, ∧, splitting ∨, ∀/∃, dependence atoms ``=(x, y)``, and
            slashed existentials ``∃y/{x} φ``. Standalone (no other flag).
        linear: if True, parse propositional intuitionistic linear logic —
            ``⊗ & ⊕ ⊸ ! 𝟙`` over atomic propositions. Standalone.
        lambek: if True, parse Lambek-calculus category types — ``• \\ /`` over
            atomic categories (``NP``, ``S``, …). Standalone.

    Mode matrix:
        (False, False) → FOL:   classical ops incl. xor (⊕), unsorted quantifiers/constants
        (True,  False) → MSFOL: classical ∧∨¬→↔⊕, sorted quantifiers/constants
        (True,  True)  → MSFL:  Łukasiewicz operators, sorted quantifiers/constants
        (False, True)  → FL:    Łukasiewicz operators, unsorted quantifiers/constants
        modal=True        → MODAL: classical unsorted FOL + modal/temporal/hybrid operators
        second_order=True → SO:    classical unsorted FOL + second-order quantifiers (∀P / ∃P)
        dependence=True   → DEP:   team-semantic dependence/IF fragment
        linear=True       → ILL:   propositional intuitionistic linear logic
        lambek=True       → L:     Lambek-calculus category types
    """

    def __init__(self, many_sorted: bool = False, fuzzy: bool = False,
                 modal: bool = False, second_order: bool = False,
                 dependence: bool = False, linear: bool = False,
                 lambek: bool = False):
        _exclusive = [name for name, flag in (
            ("dependence", dependence), ("linear", linear), ("lambek", lambek),
        ) if flag]
        if _exclusive and (many_sorted or fuzzy or modal or second_order
                           or len(_exclusive) > 1):
            raise ValueError(
                f"{_exclusive[0]}=True cannot be combined with any other mode "
                "flag; the dependence / linear / lambek modes are standalone "
                "logics with their own connectives and semantics."
            )
        if dependence:
            self._mode = "dependence"
        elif linear:
            self._mode = "linear"
        elif lambek:
            self._mode = "lambek"
        elif second_order:
            if many_sorted or fuzzy or modal:
                raise ValueError(
                    "second_order=True cannot be combined with many_sorted, fuzzy, "
                    "or modal in v1; second-order mode is classical unsorted FOL "
                    "plus second-order quantifiers over predicate variables."
                )
            self._mode = "so"
        elif modal:
            if many_sorted or fuzzy:
                raise ValueError(
                    "modal=True cannot be combined with many_sorted or fuzzy in v1; "
                    "modal mode is classical unsorted FOL plus modal operators."
                )
            self._mode = "modal"
        elif not many_sorted and not fuzzy:
            self._mode = "fol"
        elif many_sorted and not fuzzy:
            self._mode = "msfol"
        elif many_sorted and fuzzy:
            self._mode = "msfl"
        else:
            self._mode = "fl"

        # The grammar string and the matching Transformer are both assembled from
        # the operator registry for this mode — no per-mode .lark file or
        # hand-written Transformer subclass. The relative ``%import .terminals`` in
        # the generated grammar resolves against the grammars directory. The
        # registry grammar is further patched to allow single-letter
        # (VARIABLE-headed) function calls — see
        # _allow_single_letter_function_calls above.
        registry_mode = _REGISTRY_MODE[self._mode]
        cache_key = (registry_mode, len(PARSER_OPS))
        parser = _PARSER_CACHE.get(cache_key)
        if parser is None:
            grammar_text = _allow_single_letter_function_calls(build_grammar(registry_mode))
            parser = Lark(grammar_text, parser="earley",
                          import_paths=[str(_GRAMMARS_DIR)])
            _PARSER_CACHE[cache_key] = parser
        # self.parser is public: NamingError/ParsingError use parser.terminals and parser.lex()
        self.parser = parser
        self._transformer = _assemble_transformer(registry_mode)

    def parse(self, text: str) -> Node:
        """Parse a formula string and return an AST node.

        Raises:
            NamingError: lexer-level failure (unrecognized character).
            ParsingError: parser-level failure (unexpected token or EOF), or a
                transformation-level failure such as a second-order predicate
                variable applied at conflicting arities (ConflictingArityError).
        """
        try:
            tree = self.parser.parse(text)
            ast = self._transformer.transform(tree)
            ast = resolve_lambda_scope(ast)
            if self._mode == "modal":
                # A free epistemic/doxastic agent variable (K_a) denotes a named agent;
                # only an agent bound by an enclosing quantifier stays a variable.
                ast = resolve_agent_variables(ast)
            return ast
        except UnexpectedCharacters as e:
            raise NamingError(self.parser, e, text, mode=self._mode)
        except (UnexpectedToken, UnexpectedEOF) as e:
            raise ParsingError(self.parser, e, text, mode=self._mode)
        except VisitError as e:
            # A transformer handler raised. Surface a ParsingError it produced
            # (e.g. ConflictingArityError from second-order arity inference)
            # directly, rather than the opaque Lark VisitError wrapper.
            if isinstance(e.orig_exc, ParsingError):
                raise e.orig_exc
            raise
