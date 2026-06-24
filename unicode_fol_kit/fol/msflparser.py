"""MSFLParser: unified parser for FOL, MSFOL, and MSFL modes."""

import pathlib
from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from lark.exceptions import VisitError

from .nodes import Node, FOLTransformer
from ._msfl_nodes import (
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
    resolve_lambda_scope,
)
from ._fol_nodes import (
    Variable, Constant, Atom,
    build_grammar, build_transform_handlers, PARSER_OPS,
)
from ._modal_nodes import (
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until,
    Obligatory, Permitted,
)
from ._so_nodes import (
    SecondOrderQuantifier, ConflictingArityError, _infer_so_arity,
)
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


class ModalTransformer(LambdaTransformer):
    """Extends LambdaTransformer with modal, epistemic, doxastic, temporal, and deontic handlers.

    Used by modal mode (classical unsorted FOL + modal operators). Inherits all
    classical connective, term, atom, quantifier, and lambda methods. The prefix
    operators each take their leading operator token plus the single subformula;
    knows_/believes_ strip the ``K_``/``B_`` prefix from the token to recover the
    agent string. until_ builds the binary Until node. obligatory_/permitted_
    build the deontic Obligatory/Permitted nodes.
    """

    def box_(self, items):
        # items: [BOX token, formula]
        return Box(items[1])

    def diamond_(self, items):
        # items: [DIAMOND token, formula]
        return Diamond(items[1])

    def always_(self, items):
        # items: [TALWAYS token, formula]
        return Always(items[1])

    def eventually_(self, items):
        # items: [TEVENTUALLY token, formula]
        return Eventually(items[1])

    def next_(self, items):
        # items: [TNEXT token, formula]
        return Next(items[1])

    def knows_(self, items):
        # items: [KNOWS token (e.g. "K_alice"), formula]; strip the "K_" prefix.
        agent = str(items[0])[2:]
        return Knows(agent, items[1])

    def believes_(self, items):
        # items: [BELIEVES token (e.g. "B_bob"), formula]; strip the "B_" prefix.
        agent = str(items[0])[2:]
        return Believes(agent, items[1])

    def until_(self, items):
        # items: [left, TUNTIL token, right]
        return Until(items[0], items[2])

    def obligatory_(self, items):
        # items: [OBLIG token, formula]
        return Obligatory(items[1])

    def permitted_(self, items):
        # items: [PERMIT token, formula]
        return Permitted(items[1])


class SecondOrderTransformer(LambdaTransformer):
    """Extends LambdaTransformer for second-order mode.

    Adds second_order_quantifier_, which reads the bound PREDICATE token and the
    already-built body, infers the predicate variable's arity from its
    applications in the body (see _infer_so_arity), and builds a
    SecondOrderQuantifier. Inherits all classical connective, term, atom, the
    first-order quantifier_ handler, and lambda methods from LambdaTransformer.

    Lark transformers run bottom-up, so when second_order_quantifier_ fires the
    body is a fully-built AST node (including any nested SecondOrderQuantifier),
    which _infer_so_arity can walk directly.
    """

    def second_order_quantifier_(self, items):
        # Grammar: (FORALL | EXISTS) PREDICATE negation -> second_order_quantifier_
        # items[0] is the FORALL/EXISTS token; items[1] is the PREDICATE token
        # (no terminal handler, so a raw Token); items[2] is the body node.
        quant = str(items[0])
        predname = str(items[1])
        body = items[2]
        arity = _infer_so_arity(body, predname)
        return SecondOrderQuantifier(quant, predname, arity, body)


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
            return resolve_lambda_scope(ast)
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
