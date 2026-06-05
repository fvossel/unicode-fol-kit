"""MSFLParser: unified parser for FOL, MSFOL, and MSFL modes."""

import pathlib
from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF

from .nodes import Node, FOLTransformer
from ._msfl_nodes import (
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
    resolve_lambda_scope,
)
from ._fol_nodes import Variable, Constant
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


class MSFOLTransformer(LambdaTransformer):
    """Extends LambdaTransformer for MSFOL mode.

    Adds sorted_quantifier_ and sorted_const_.  Inherits all classical
    connective, term, and lambda methods; the MSFOL grammar never emits
    xor_ or quantifier_, so those inherited methods are safe-dead.
    """

    def sorted_quantifier_(self, items):
        quant_tok, var, sort_tok, formula = items
        sort = str(sort_tok)[1:]  # strip leading ':'
        return SortedQuantifier(str(quant_tok), var, sort, formula)

    def sorted_const_(self, items):
        first, sort_tok = items
        # NAME tokens are pre-converted to Constant by FOLTransformer.NAME();
        # CONSTANT tokens arrive as raw Token objects.
        name = first.name if isinstance(first, Constant) else str(first)
        sort = str(sort_tok)[1:]  # strip leading ':'
        return SortedConstant(name, sort)


class LukConnectivesMixin:
    """Łukasiewicz connective handlers shared by MSFLTransformer and FLTransformer.

    Must be mixed into a class that provides _fold_binary (any FOLTransformer descendant),
    since this mixin calls self._fold_binary but does not define it itself.
    """

    def luk_not_(self, items):
        return LukNegation(items[0])

    def luk_implies_(self, items):
        return LukImplication(items[0], items[1])

    def luk_iff_(self, items):
        return LukEquivalence(items[0], items[1])

    def weak_and_(self, items):
        return self._fold_binary(items, WeakConjunction)

    def weak_or_(self, items):
        return self._fold_binary(items, WeakDisjunction)

    def strong_and_(self, items):
        return self._fold_binary(items, StrongConjunction)

    def strong_or_(self, items):
        return self._fold_binary(items, StrongDisjunction)


class MSFLTransformer(LukConnectivesMixin, MSFOLTransformer):
    """Extends MSFOLTransformer for MSFL (fuzzy Łukasiewicz) mode.

    Inherits sorted_quantifier_, sorted_const_, and all term/atom methods from
    the MSFOLTransformer ancestry.  Inherits the seven Łukasiewicz connective
    handlers from LukConnectivesMixin.  The MSFL grammar uses luk_*/weak_*/
    strong_* rule aliases so the inherited classical connective methods
    (and_, or_, not_, etc.) are safe-dead.

    MRO: MSFLTransformer → LukConnectivesMixin → MSFOLTransformer →
         LambdaTransformer → FOLTransformer → Transformer
    """


class FLTransformer(LukConnectivesMixin, LambdaTransformer):
    """Transformer for FL mode (single-sorted Łukasiewicz logic, unsorted quantifiers).

    Inherits lambda_, application_, and all classical term/atom methods from
    LambdaTransformer (via FOLTransformer) — including the unsorted quantifier_
    handler.  Inherits the seven Łukasiewicz connective handlers from
    LukConnectivesMixin.  Has no sorted_quantifier_ or sorted_const_; FL uses
    plain quantifiers and constants identical to FOL mode.

    MRO: FLTransformer → LukConnectivesMixin → LambdaTransformer →
         FOLTransformer → Transformer
    """


class MSFLParser:
    """Unified parser supporting FOL, MSFOL, MSFL, and FL modes.

    Args:
        many_sorted: if True, quantifiers and constants must carry sort
            annotations (e.g. ``∀x:Human P(x)``, ``alice:Human``).
        fuzzy: if True, use Łukasiewicz operators (⊗ ⊕ for strong
            conjunction/disjunction; ¬ → ↔ map to Łukasiewicz nodes).

    Mode matrix:
        (False, False) → FOL:   classical ops incl. xor (⊕), unsorted quantifiers/constants
        (True,  False) → MSFOL: classical ∧∨¬→↔ (no xor), sorted quantifiers/constants
        (True,  True)  → MSFL:  Łukasiewicz operators, sorted quantifiers/constants
        (False, True)  → FL:    Łukasiewicz operators, unsorted quantifiers/constants
    """

    def __init__(self, many_sorted: bool = False, fuzzy: bool = False):
        if not many_sorted and not fuzzy:
            grammar_file = "fol.lark"
            self._transformer = LambdaTransformer()
            self._mode = "fol"
        elif many_sorted and not fuzzy:
            grammar_file = "msfol.lark"
            self._transformer = MSFOLTransformer()
            self._mode = "msfol"
        elif many_sorted and fuzzy:
            grammar_file = "msfl.lark"
            self._transformer = MSFLTransformer()
            self._mode = "msfl"
        else:
            grammar_file = "fl.lark"
            self._transformer = FLTransformer()
            self._mode = "fl"

        # self.parser is public: NamingError/ParsingError use parser.terminals and parser.lex()
        self.parser = Lark.open(str(_GRAMMARS_DIR / grammar_file), parser="earley")

    def parse(self, text: str) -> Node:
        """Parse a formula string and return an AST node.

        Raises:
            NamingError: lexer-level failure (unrecognized character).
            ParsingError: parser-level failure (unexpected token or EOF).
        """
        try:
            tree = self.parser.parse(text)
            ast = self._transformer.transform(tree)
            return resolve_lambda_scope(ast)
        except UnexpectedCharacters as e:
            raise NamingError(self.parser, e, text, mode=self._mode)
        except (UnexpectedToken, UnexpectedEOF) as e:
            raise ParsingError(self.parser, e, text, mode=self._mode)
