"""MSFLParser: unified parser for FOL, MSFOL, and MSFL modes."""

import pathlib
from lark import Lark, Token, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from lark.exceptions import VisitError

from .nodes import Node, FOLTransformer
from ._msfl_nodes import LambdaVar, Lambda, Application, resolve_lambda_scope
from ._fol_nodes import (
    Variable, Constant, Function,
    build_grammar, build_transform_handlers, PARSER_OPS,
    OPERATORS, parser_ops_for_mode,
)
from ._modal_nodes import resolve_agent_variables
from ._so_nodes import ConflictingArityError  # re-exported for callers/tests
from .naming import NamingError, ParsingError
from .spans import (
    SpannedFormula,
    span_from_meta, span_from_token, make_span, find_glyph,
    trim_ws_backward, fill_gap_spans, build_span_map, project_spans,
)

_GRAMMARS_DIR = pathlib.Path(__file__).parent / "grammars"


def _safe_find_glyph(text: str, start: int, end: int, glyph: str):
    """``spans.find_glyph``, but degrading to ``None`` instead of raising.

    Every call site below is guarded by ``spans.find_glyph``'s own
    grammar-guaranteed invariant (the glyph really is the sole non-parens
    content between two adjacent operands) — this should never actually
    fail for a tree the parser itself produced. It is wrapped anyway so a
    span-derivation edge case degrades to that ONE occurrence reporting
    UNKNOWN rather than turning an opt-in, best-effort feature into a hard
    failure of parse_with_spans itself.
    """
    try:
        return find_glyph(text, start, end, glyph)
    except ValueError:
        return None


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


# =========================
# Span-capturing transform (used only by MSFLParser.parse_with_spans)
# =========================
#
# Lark's Transformer routes EVERY rule reduction through _call_userfunc(tree,
# new_children) and every token through _call_userfunc_token(token) (see
# lark.visitors.Transformer) — tree.meta (with propagate_positions=True, set
# above) and the token itself both already carry exact source positions.
# Overriding just these two dispatch hooks lets us record spans for whatever
# Node each already-existing handler produces, WITHOUT changing a single
# handler in FOLTransformer / LambdaTransformer / the operator registry: every
# rule alias still runs exactly the function build_transform_handlers attaches
# for plain parse() (level2/fold aliases are the one exception — see
# _fold_level2 below — and even those build the exact same node graph
# _fold_binary would, just with span bookkeeping alongside), we just
# additionally look at the Tree/Token that was being reduced once the
# (unmodified) handler has returned.
#
# TWO id()-keyed dicts are built (id_extent, id_head) — see spans.py's
# build_span_map docstring for why id() is fine here: it is a transient,
# same-call-only bookkeeping device, never exposed past this transform. Once
# the whole tree has been transformed, MSFLParser.parse_with_spans turns
# these into the PATH-keyed, spec-correct SpanMap it actually returns.
#
# HEAD SPANS — THE LARK-FILTERING PROBLEM AND WHY THIS DOES NOT USE
# keep_all_tokens=True
# ---------------------------------------------------------------------------
# Every classical connective (¬ ∧ ∨ → ↔ ⊕) and every infix comparison
# (= < > ≤ ≥ ≠) is declared as an ANONYMOUS string-literal terminal inline in
# the grammar (e.g. '"¬" prefix' -> not_), and Lark auto-filters an anonymous
# literal out of the parse tree by default — so its own token never reaches
# _call_userfunc's new_children, and there is no tree.meta for the head
# position on its own (only the whole rule's meta is available).
#
# The obvious fix, building the span parser with keep_all_tokens=True, was
# tried and rejected: it does not just ADD the filtered tokens back, it also
# defeats Lark's "?rule inlines away when it reduces to one child after
# filtering" mechanism that '?prefix: … | "(" formula ")"' relies on to make
# a parenthesised subexpression collapse straight through to its inner
# node — with keep_all_tokens=True the "(" and ")" survive as extra children,
# the alternative no longer has one child, so it stops inlining and instead
# becomes an un-aliased Tree('prefix', [...]) with NO transform handler
# (Transformer.__default__ returns it as a bare Tree, not a Node) — breaking
# AST construction for every parenthesised subformula. It was also going to
# require a SECOND compiled Lark parser (a second Earley grammar build),
# which the "do not change parse()'s performance" requirement rules out for
# the shared, cached self.parser — and a keep_all_tokens tree also does not
# feed the mode's OWN registered handlers (not_, and_, …) unmodified, since
# those handlers are written for the filtered item shape; reusing them would
# need re-deriving the filtering by hand anyway.
#
# So this uses the parser exactly as parse() does (propagate_positions,
# no keep_all_tokens, same cached Lark instance — parse()'s own behaviour and
# performance are untouched) and recovers each head position from what IS
# already available without keep_all_tokens:
#   * FORALL/EXISTS, COUNTOP: NAMED terminals are never auto-filtered, so the
#     raw Token is already sitting in new_children — no scan needed. A
#     quantifier's head is [that token's start, the bound Variable's own
#     already-known extent end) — which is exactly "symbol + variable +
#     whatever whitespace sits between them", satisfying A5 directly.
#   * PREDICATE (an atom's head): also a named terminal, same story — the raw
#     token is new_children[0] for atom_/atom0_.
#   * A prefix op's glyph (¬, and any future one driven by the OPERATORS
#     registry's fixity=="prefix"): always the FIRST thing the rule matches
#     (tree.meta.start_pos), so the head is simply
#     [meta.start_pos, meta.start_pos + len(glyph)) — no scan needed either.
#   * A binary infix glyph (→, ↔, and every comparison predicate) and a
#     same-level fold's connective (∧, ∨, ⊕, Ⓒ): genuinely filtered, with no
#     token anywhere to read a position off. These are located by
#     spans.find_glyph, searching the SOURCE TEXT for the operator's own
#     glyph within the gap between the two operands' own already-known
#     (inner) extents. That gap can be WIDER than "just whitespace" — an
#     operand may carry its own redundant wrapping parentheses, which its
#     inner extent (per A5 item 3) deliberately excludes — but find_glyph
#     searches for the EXACT glyph text rather than "the first non-whitespace
#     run", which is what makes that safe (no parenthesis can equal the
#     glyph). See spans.find_glyph's docstring.
#
# A SAME-LEVEL FOLD gets special handling on top of this (_fold_level2): only
# the OUTERMOST fold result is directly dispatched by Lark (see
# spans.py's module docstring for why), so every INTERMEDIATE left-fold node
# is built manually here, in lockstep with locating each connective
# occurrence — see _fold_level2's own docstring for why the intermediate's
# own EXTENT cannot be the naive union of its two operands' inner extents
# either (same "an operand may have its own wrapping parens" problem, this
# time for extent rather than head).
#
# This mixin sits BEFORE LambdaTransformer in MRO, so its super() calls reach
# Transformer's real dispatch, which looks up handlers via getattr(self, ...)
# — INSTANCE attributes (the setattr'd registry handlers) are found exactly as
# for a plain LambdaTransformer instance; only the dispatch hooks below differ.

#: rule_alias -> the exact glyph text for every "binary, single occurrence,
#: filtered-anonymous-literal" operator this transform locates via
#: spans.find_glyph: the classical infix comparisons and the arithmetic term
#: operators (neither driven by the OPERATORS registry, which only covers
#: FORMULA operators, not the term layer's infix predicates/functions) plus
#: the two binary connective levels (→, ↔ — these ARE registry-driven; see
#: _binary_glyph below, which merges this with the registry so both paths
#: share one lookup). The arithmetic entries give a Function("+"/"-"/"*"/"/",
#: …) node — built by the SAME shared term layer as any other function, so
#: its head is that operator occurrence, exactly like an infix comparison's.
_INFIX_TERM_GLYPH = {
    "eq_": "=", "lt_": "<", "gt_": ">", "le_": "≤", "ge_": "≥", "ne_": "≠",
    "add_": "+", "sub_": "-", "mul_": "*", "div_": "/",
}


class _SpanCapturingTransform:
    """Mixin: record precise (extent, head) spans for every Node a rule/token
    handler builds, keyed transiently by id() — see the module comment above
    and spans.py's ``build_span_map`` docstring for why id() here is safe.

    ``self.id_extent`` / ``self.id_head`` (``id(node) -> spans.Span``) are
    populated as a side effect of ``transform()``; the caller
    (``MSFLParser.parse_with_spans``) turns them into a path-keyed
    :class:`~unicode_fol_kit.fol.spans.SpanMap` once transform() returns. See
    spans.py's module docstring for the two cases this alone cannot recover
    (an agent variable sliced out of a combined K_a-style token; a
    higher-order lambda rewrite) — both report :data:`~unicode_fol_kit.fol.spans.UNKNOWN`.
    """

    def __init__(self, text: str, registry_mode: str, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._span_text = text
        self.id_extent: dict = {}
        self.id_head: dict = {}

        # Registry-driven lookup tables, built once per transformer instance
        # from this mode's ParserOps: which rule aliases are same-level folds
        # (and which Node class/glyph each folds into), and which are a
        # non-folded connective driven by the OPERATORS registry (fixity ==
        # "prefix" | "binary_implies" | "binary_iff" | "binary_until" — every
        # OTHER fixity, notably "agent_prefix", is deliberately excluded: its
        # token is not a bare glyph, see the module comment's UNKNOWN case).
        self._level2_cls: dict = {}
        self._binary_glyph: dict = dict(_INFIX_TERM_GLYPH)
        for op in parser_ops_for_mode(registry_mode):
            if op.level == "level2":
                self._level2_cls[op.rule_alias] = op.node_class
                continue
            spec = OPERATORS.get(op.node_class.__name__)
            if spec is not None and spec.fixity in (
                    "binary_implies", "binary_iff", "binary_until"):
                self._binary_glyph[op.rule_alias] = spec.unicode

    def _call_userfunc(self, tree, new_children=None):
        text = self._span_text
        alias = str(tree.data)
        children = tree.children if new_children is None else new_children

        if alias in self._level2_cls:
            return self._fold_level2(alias, self._level2_cls[alias], children, tree.meta)

        result = super()._call_userfunc(tree, children)
        if not isinstance(result, Node):
            return result
        if not tree.meta.empty:
            self.id_extent[id(result)] = span_from_meta(tree.meta, text)
        self._assign_head(alias, tree, children, result)
        return result

    def _call_userfunc_token(self, token):
        result = super()._call_userfunc_token(token)
        if isinstance(result, Node):
            span = span_from_token(token, self._span_text)
            self.id_extent[id(result)] = span
            self.id_head[id(result)] = span  # a leaf term IS its own head
        return result

    # -- head-span derivation, per rule shape ----------------------------

    def _assign_head(self, alias, tree, children, result):
        """Set ``self.id_head[id(result)]`` for one directly-dispatched
        (non-fold) rule reduction, using whichever mechanism the module
        comment above documents for ``alias``'s shape. A rule this covers
        no case for (out of this change's target fragment) is simply left
        without a head entry — reported as UNKNOWN, never guessed."""
        text = self._span_text

        if alias in ("atom_", "atom0_"):
            # PREDICATE is a named terminal: never filtered, already a raw
            # Token in children[0] (no per-token handler turns it into a Node).
            tok = children[0]
            if isinstance(tok, Token):
                self.id_head[id(result)] = span_from_token(tok, text)
            return

        if alias in ("const_", "number_"):
            # CONSTANT / NUMBER also have no per-token handler, so the raw
            # token — the leaf's ENTIRE span — is still sitting in children[0].
            tok = children[0]
            if isinstance(tok, Token):
                span = span_from_token(tok, text)
                self.id_extent[id(result)] = span
                self.id_head[id(result)] = span
            return

        if alias == "function_":
            # The function name occupies whatever leaf (Constant/Variable
            # Node, already span-captured; or a raw Token in an edge case)
            # was consumed as children[0] — that leaf's own span IS the
            # function's head.
            head_src = children[0]
            if isinstance(head_src, Node) and id(head_src) in self.id_extent:
                self.id_head[id(result)] = self.id_extent[id(head_src)]
            elif isinstance(head_src, Token):
                self.id_head[id(result)] = span_from_token(head_src, text)
            return

        if alias == "quantifier_":
            self._assign_binder_head(children[0], children[1], result)
            return

        if alias == "count_":
            # COUNTOP NUMBER VARIABLE prefix -> the head runs from COUNTOP's
            # own start through the bound VARIABLE's end (COUNTOP and the
            # bound NUMBER are both named terminals, but only the VARIABLE's
            # end matters for the head's right edge — "∃≥3 y").
            self._assign_binder_head(children[0], children[2], result)
            return

        if alias in self._binary_glyph:
            left, right = children[0], children[1]
            le = self.id_extent.get(id(left))
            re_ = self.id_extent.get(id(right))
            if le is not None and re_ is not None:
                found = _safe_find_glyph(text, le.end, re_.start, self._binary_glyph[alias])
                if found is not None:
                    self.id_head[id(result)] = make_span(text, *found)
            return

        spec = OPERATORS.get(type(result).__name__)
        if spec is not None and spec.fixity == "prefix" and not tree.meta.empty:
            s = tree.meta.start_pos
            self.id_head[id(result)] = make_span(text, s, s + len(spec.unicode))
            return
        # Any other alias (agent_prefix, binders outside quantifier_/count_,
        # lambda_/application_, out-of-fragment term forms, …): no rule here,
        # head stays UNKNOWN for this node.

    def _assign_binder_head(self, symbol_tok, var_node, result):
        """Shared by quantifier_/count_: head = [symbol_tok.start_pos,
        var_node's own extent end) — the binder symbol together with its
        bound variable, whitespace between them included (A5)."""
        text = self._span_text
        ve = self.id_extent.get(id(var_node))
        if isinstance(symbol_tok, Token) and ve is not None:
            self.id_head[id(result)] = make_span(text, symbol_tok.start_pos, ve.end)

    # -- same-level operator-chain folding, WITH span bookkeeping ---------

    def _fold_level2(self, alias, node_cls, items, meta):
        """Left-fold ``items`` into nested ``node_cls`` binary nodes — same
        node graph ``FOLTransformer._fold_binary`` builds (deterministic,
        pure function of ``items``/``node_cls``, so building it here instead
        of delegating produces a structurally identical AST) — while
        additionally recording (extent, head) for every INTERMEDIATE node,
        not just the outermost one Lark itself dispatches (see the module
        comment's "A SAME-LEVEL FOLD" section).

        Each connective's HEAD is found once per gap, from the ORIGINAL
        operands' own (already-known) inner extents — safe even when an
        operand carries its own redundant wrapping parens, same reasoning as
        find_glyph's docstring.

        Each intermediate's EXTENT is NOT the naive union of its two
        operands' inner extents — an operand's inner extent deliberately
        excludes redundant wrapping parens (A5 item 3), so if operand k is
        individually parenthesised, "union of inner extents" would slice
        THROUGH that closing paren and the next operand's opening paren,
        producing a non-reparseable fragment (e.g. "(P) ∧ (Q)" would wrongly
        shrink to "P) ∧ (Q"). Instead every intermediate STARTS at the whole
        fold's own start (meta.start_pos — exactly operand 0's true outer
        bound, parens included, since operand 0 begins the rule's own match)
        and ENDS either at the position right before the NEXT connective
        (whitespace-trimmed backward — exactly operand k's true outer bound)
        for a non-final intermediate, or at the whole fold's own end
        (meta.end_pos) for the final one — both of which correctly include
        any wrapping parens an operand happens to have, because they are
        read off the ACTUAL SOURCE TEXT / the whole rule's own Lark-computed
        bounds rather than reconstructed from the operands' narrowed inner
        extents.
        """
        text = self._span_text
        glyph = OPERATORS[node_cls.__name__].unicode
        n = len(items)

        # Every connective's (start, end), found once, in left-to-right order.
        glyph_spans = []
        for j in range(n - 1):
            le = self.id_extent.get(id(items[j]))
            re_ = self.id_extent.get(id(items[j + 1]))
            glyph_spans.append(
                _safe_find_glyph(text, le.end, re_.start, glyph)
                if le is not None and re_ is not None else None)

        outer_start = meta.start_pos if not meta.empty else None
        outer_end = meta.end_pos if not meta.empty else None

        node = items[0]
        for j in range(n - 1):
            node = node_cls(node, items[j + 1])
            gspan = glyph_spans[j]
            if gspan is not None:
                self.id_head[id(node)] = make_span(text, *gspan)
            if outer_start is None:
                continue  # no rule meta at all (should not happen) -> extent left to fill_gap_spans
            if j == n - 2:
                end = outer_end
            elif glyph_spans[j + 1] is not None:
                end = trim_ws_backward(text, glyph_spans[j + 1][0])
            else:
                end = None
            if end is not None:
                self.id_extent[id(node)] = make_span(text, outer_start, end)
        return node


class _SpanLambdaTransformer(_SpanCapturingTransform, LambdaTransformer):
    """LambdaTransformer with span capture mixed in; see _SpanCapturingTransform."""

    def lambda_(self, items):
        """``LambdaTransformer.lambda_`` plus a span for the bound parameter.

        The base handler reads the parameter out of ``items[1]`` and then
        builds a FRESH ``LambdaVar`` from its name, discarding the node (or
        raw PREDICATE token) it came from. That new object never passes
        through Lark's dispatch hooks, so the mixin never sees it — and
        because ``LambdaVar`` is a leaf, ``fill_gap_spans`` cannot derive
        its span from children either. Without this override the parameter
        of EVERY lambda, ordinary ones included, would report UNKNOWN while
        its source position (``λx. …`` -> the ``x``) sits right there in
        ``items[1]``.

        Overridden here rather than in ``LambdaTransformer`` on purpose:
        this subclass exists only for the span pass, so plain ``parse()``
        keeps running the untouched handler.
        """
        result = super().lambda_(items)
        param_source = items[1]
        span = None
        if isinstance(param_source, Node):
            span = self.id_extent.get(id(param_source))
        elif isinstance(param_source, Token):
            span = span_from_token(param_source, self._span_text)
        if span is not None and isinstance(result, Lambda):
            self.id_extent[id(result.param)] = span
            self.id_head[id(result.param)] = span  # leaf: head == extent
        return result


def _assemble_span_transformer(registry_mode: str, text: str) -> _SpanLambdaTransformer:
    """Span-capturing sibling of _assemble_transformer, for the same registry_mode.

    Attaches the SAME per-mode operator handlers (build_transform_handlers) as
    _assemble_transformer — parse_with_spans builds an AST byte-identical to
    parse()'s, just with spans recorded alongside.
    """
    transformer = _SpanLambdaTransformer(text, registry_mode)
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
            # propagate_positions=True costs nothing parse()-observable — it only
            # adds a `.meta` (start_pos/end_pos/line/column/end_line/end_column)
            # to every Tree Lark builds, which plain parse() never looks at. It is
            # what parse_with_spans (below) reads to build its SpanMap; verified
            # empirically (see spans.py's module docstring / the "prove it on a
            # real example" section of this change's report) that Lark's Earley
            # parser populates it accurately, including for Tokens, without
            # needing anything beyond this flag.
            parser = Lark(grammar_text, parser="earley",
                          import_paths=[str(_GRAMMARS_DIR)],
                          propagate_positions=True)
            _PARSER_CACHE[cache_key] = parser
        # self.parser is public: NamingError/ParsingError use parser.terminals and parser.lex()
        self.parser = parser
        self._transformer = _assemble_transformer(registry_mode)
        self._registry_mode = registry_mode  # parse_with_spans re-derives its own transformer from this

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

    def parse_with_spans(self, text: str) -> SpannedFormula:
        """Parse ``text`` like :meth:`parse`, and also return a source-span side table.

        Returns a :class:`~unicode_fol_kit.fol.spans.SpannedFormula` — ``.formula``
        is exactly what ``parse(text)`` would return (same AST, unchanged; this
        method runs the SAME cached ``self.parser`` and the same
        ``resolve_lambda_scope``/``resolve_agent_variables`` rewrites — the span
        bookkeeping is additive, nothing about how the AST itself is built
        changes), and ``.spans`` is a :class:`~unicode_fol_kit.fol.spans.SpanMap`
        keyed by PATH — see :mod:`unicode_fol_kit.fol.spans`'s module docstring
        for the path convention and why a path (not a node, not an id()) is the
        key. Raises the same exceptions as :meth:`parse`, for the same reasons.

        Look a node's spans up either via its path (``spans.get(path)``, ``path``
        from :func:`~unicode_fol_kit.fol.spans.traverse`) or, for a node object
        already in hand, ``spans.for_node(node)`` — see
        :class:`~unicode_fol_kit.fol.spans.SpanMap`. Either field of the
        returned :class:`~unicode_fol_kit.fol.spans.NodeSpans` (``.extent``/
        ``.head``) may individually be :data:`~unicode_fol_kit.fol.spans.UNKNOWN`
        — never a guessed or interpolated span — for a documented, narrow set of
        cases (out-of-fragment operators; an agent variable sliced out of a
        combined ``K_a``-style token; a higher-order lambda application
        rewritten into a fresh Application/LambdaVar chain the original parse
        never produced) — see spans.py's module docstring for the full
        case-by-case argument. For the classical FOL fragment (∀ ∃ ¬ ∧ ∨ → ↔ ⊕,
        predicates over constants/variables/function terms) both fields are
        recovered exactly for every node.
        """
        try:
            tree = self.parser.parse(text)
            span_transformer = _assemble_span_transformer(self._registry_mode, text)
            pre_ast = span_transformer.transform(tree)
            id_extent = span_transformer.id_extent
            id_head = span_transformer.id_head
            fill_gap_spans(pre_ast, id_extent, text)
            spans = build_span_map(pre_ast, id_extent, id_head)
            ast = resolve_lambda_scope(pre_ast)
            spans = project_spans(pre_ast, ast, spans)
            if self._mode == "modal":
                post_ast = resolve_agent_variables(ast)
                spans = project_spans(ast, post_ast, spans)
                ast = post_ast
            return SpannedFormula(ast, spans)
        except UnexpectedCharacters as e:
            raise NamingError(self.parser, e, text, mode=self._mode)
        except (UnexpectedToken, UnexpectedEOF) as e:
            raise ParsingError(self.parser, e, text, mode=self._mode)
        except VisitError as e:
            if isinstance(e.orig_exc, ParsingError):
                raise e.orig_exc
            raise
