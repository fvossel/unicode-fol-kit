"""MSFLParser: unified parser for FOL, MSFOL, and MSFL modes."""

import pathlib
from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from lark.exceptions import VisitError

from .nodes import Node, FOLTransformer
from ._msfl_nodes import LambdaVar, Lambda, Application, resolve_lambda_scope
from ._fol_nodes import (
    Variable, Constant,
    build_grammar, build_transform_handlers, PARSER_OPS,
)
from ._modal_nodes import resolve_agent_variables
from ._so_nodes import ConflictingArityError  # re-exported for callers/tests
from .naming import NamingError, ParsingError

_GRAMMARS_DIR = pathlib.Path(__file__).parent / "grammars"


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

    Mode matrix:
        (False, False) → FOL:   classical ops incl. xor (⊕), unsorted quantifiers/constants
        (True,  False) → MSFOL: classical ∧∨¬→↔ (no xor), sorted quantifiers/constants
        (True,  True)  → MSFL:  Łukasiewicz operators, sorted quantifiers/constants
        (False, True)  → FL:    Łukasiewicz operators, unsorted quantifiers/constants
        modal=True        → MODAL: classical unsorted FOL + modal/temporal operators
        second_order=True → SO:    classical unsorted FOL + second-order quantifiers (∀P / ∃P)
    """

    def __init__(self, many_sorted: bool = False, fuzzy: bool = False,
                 modal: bool = False, second_order: bool = False):
        if second_order:
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
        # the generated grammar resolves against the grammars directory.
        registry_mode = _REGISTRY_MODE[self._mode]
        cache_key = (registry_mode, len(PARSER_OPS))
        parser = _PARSER_CACHE.get(cache_key)
        if parser is None:
            parser = Lark(build_grammar(registry_mode), parser="earley",
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
