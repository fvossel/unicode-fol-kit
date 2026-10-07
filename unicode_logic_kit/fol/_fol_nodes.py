"""Z3 environment, base Node class, classical FOL nodes, registry, and Lark transformer."""

import contextvars
import functools
import re
import types
from decimal import Decimal
from typing import Any, Callable, List, Optional, Tuple, TypeVar, Union, Dict, cast
from lark import Transformer
from dataclasses import dataclass, fields

import z3

from . import _identifiers
from ._tptp_symbols import check_variable_names as _check_variable_names
from ._tptp_symbols import guard_class as _guard_to_tptp
from ._tptp_symbols import is_tptp_boolean_atom as _is_tptp_boolean_atom
from ._tptp_symbols import truth_constant_word as _truth_constant_word
from .naming import ParsingError

_SORT = z3.DeclareSort("S")


def numeral_key(value) -> str:
    """The text a numeral is known by: ONE text per VALUE.

    ``Number(1) == Number(1.0)`` is ``True`` in the kit (the two hash alike), so ``1``, ``1.0``
    and ``01`` are one numeral and a route that makes a constant of a numeral makes ONE
    constant of them. An integral value is written as an integer (``1.0`` and ``1`` are
    ``'1'``, ``-0.0`` is ``'0'``), any other value as ``str`` of it (``'2.5'``, ``'-1'``,
    ``'1e-07'``). Two numerals have the same key exactly when they are equal.

    A :class:`Number` already stores an integral float as the integer it equals, so the key of
    a node's value is ``str`` of it; the function takes any value, a raw ``1.0`` too.
    """
    if isinstance(value, bool):
        value = int(value)
    elif isinstance(value, float) and value.is_integer():
        value = int(value)
    return str(value)


#: What a Z3 name ends in when the symbol is a VARIABLE (``x`` is written ``x!v``), and what a
#: constant whose own name already ends that way, or in this, gets appended (``x!v`` is written
#: ``x!v!c``). A variable's name always ends in the first mark and a constant's never does, so a
#: constant and a variable of one name are two symbols, and the two maps are injective.
_VARIABLE_MARK = "!v"
_ESCAPE_MARK = "!c"


def z3_constant_name(name: str) -> str:
    """The name of the Z3 symbol of the constant ``name``: the name itself, except for a name
    that ends in ``!v`` or ``!c``, which gets ``!c`` appended so that no constant is spelled
    like a variable's symbol (see :func:`z3_variable_name`)."""
    return name + _ESCAPE_MARK if name.endswith((_VARIABLE_MARK, _ESCAPE_MARK)) else name


def z3_variable_name(name: str) -> str:
    """The name of the Z3 symbol of the variable ``name``: ``name`` followed by ``!v``."""
    return name + _VARIABLE_MARK


def kit_name_of_z3_symbol(z3_name: str) -> Tuple[str, bool]:
    """Read the name of a Z3 constant of sort ``S`` back as ``(kit name, is it a variable)``.

    The inverse of :func:`z3_variable_name` and of :func:`z3_constant_name`, and of nothing
    else: ``x!v`` is the variable ``x``, ``x!v!c`` the constant ``x!v``, ``x`` the constant
    ``x``. A name that neither writer produces is a constant of exactly that name: ``x!c``
    is not written for any constant (the constant ``x`` is written ``x``, and only a name
    that already ends in a mark gets ``!c`` appended), so a text that holds the symbols
    ``x`` and ``x!c`` reads them as two constants, ``x`` and ``x!c``, never as one. The
    function reads ONE name, so it is no more than the inverse of the writers: a text that holds
    ``a!c`` (no writer's) and ``a!c!c`` (the writer's name of the constant ``a!c``) would be read
    as one constant, ``a!c``, by calling it on each; the reader of a text
    (:func:`~unicode_logic_kit.atp.z3_input.from_z3`) reads the second as written, ``a!c!c``.
    Only the names of the nullary symbols of sort ``S`` are written this way (a function, a
    predicate and a proposition keep their names), so only those are to be read with it.
    """
    if z3_name.endswith(_VARIABLE_MARK):
        return z3_name[:-len(_VARIABLE_MARK)], True
    if z3_name.endswith(_ESCAPE_MARK):
        stripped = z3_name[:-len(_ESCAPE_MARK)]
        if stripped.endswith((_VARIABLE_MARK, _ESCAPE_MARK)):
            return stripped, False
    return z3_name, False


def check_z3_name(name: str) -> None:
    """Refuse a symbol name that the Z3 C API cannot carry.

    Z3 reads a name as a C string: it ends at the first NUL character, so ``a\\x00b`` and
    ``a\\x00c`` would be the one symbol ``a``, and a lone surrogate (which no UTF-8 text
    holds) makes the call raise ``UnicodeEncodeError``. A problem that names two things
    alike is not the problem that was asked, so the name is refused before anything is
    declared, by every translation into Z3 (:class:`Z3Env`, the arithmetic environment).

    Raises:
        NotImplementedError: the name holds a NUL character or a lone surrogate.
    """
    if "\x00" in name:
        raise NotImplementedError(
            f"to_z3: the name {name!r} holds a NUL character, which Z3 reads as the end of a name "
            f"(so it would be the symbol {name.split(chr(0))[0]!r}). Rename the symbol.")
    try:
        name.encode("utf-8")
    except UnicodeEncodeError:
        raise NotImplementedError(
            f"to_z3: the name {name!r} holds a lone surrogate, which is no text that Z3 can take "
            f"as the name of a symbol. Rename the symbol.") from None


def numeral_constant_clash(text: str):
    """Refuse a numeral and a constant that are one symbol.

    A numeral is translated to the symbol of its own text (:func:`numeral_key`), so
    ``Number(1)`` and a constant named ``1`` (``Constant('1')``) are the same Z3
    symbol and ``P(1)`` would say what ``P('1')`` says. The problem writers for TPTP
    refuse the pair for the same reason. Raised by :class:`Z3Env` and by the cvc5
    sanitiser. A VARIABLE spelled like a numeral is another symbol and is not refused.

    Raises:
        NotImplementedError: always, naming the text and what to do instead.
    """
    raise NotImplementedError(
        f"to_z3: the numeral {text} and a constant named {text!r} are one symbol "
        f"(a numeral is the symbol of its own text), so the problem would say about one "
        f"thing what it says about two. Rename the constant, or write the number as a "
        f"constant of another name.")


# =========================
# Z3 Environment
# =========================

class Z3Env:
    """Tracks declared Z3 symbols. Single sort for all terms.

    **What is one symbol.** A constant is keyed on its name; a function and a
    predicate on ``(name, arity)`` each, in a table of their own. So ``P(a)`` and
    ``P(a, b)`` are two predicates, ``f(a)`` and ``f(a, b)`` two functions,
    ``P(f(a))`` with a predicate ``P`` and a function ``P`` two symbols, and the
    guard predicate ``Car`` of a sort (arity 1) is not the predicate ``Car`` of
    ``Car(x, y)`` (arity 2). A function of no arguments is the constant of its name;
    a predicate of no arguments (a proposition) is not.

    **A variable is a symbol of its own.** A :class:`~unicode_logic_kit.fol.nodes.Variable`
    and a :class:`~unicode_logic_kit.fol.nodes.Constant` of one name are two symbols, in
    every position: the quantifier of ``∀x P(x, c)`` with ``c = Constant('x')`` binds the
    variable and leaves the constant alone. The Z3 symbol of the variable ``x`` is named
    ``x!v`` and a constant's is named as it is, except that a constant whose name ends in
    ``!v`` or ``!c`` gets ``!c`` appended (:func:`z3_constant_name`), so no constant can be
    spelled like a variable's symbol, and the naming needs no state: two environments, or
    two translations with no environment at all, agree on every name. ``variables_apart=False``
    names a variable as it is named, like a constant; it is for a caller that has already
    given every symbol of the problem a name of its own, in ONE namespace (the SMT-LIB text
    routes do: their sanitiser gives every predicate, function, constant and variable a token
    that no other has, and none that ends in ``!v`` or ``!c``, and they lower every counting
    quantifier before they sanitise, so that the witnesses are in that namespace too) and wants
    the text to hold the names it writes. A name minted for this environment by a ``to_z3``
    method (the witnesses of a counting quantifier, the variable of a sort-axiom) is a
    variable, so with the default naming it is a symbol ``x0!v`` that no name of a problem can
    be, and needs no avoid set.

    **One exception, refused.** The numeral ``Number(1)`` is written as the symbol of its
    VALUE (``Number(1.0)`` is the same constant, see :func:`numeral_key`), which is also what
    a constant named ``1`` is, so the two would be ONE Z3 symbol and ``P(1)`` would say the
    same as ``P('1')`` (a TPTP writer refuses the pair for the same reason). The environment
    remembers which kind of node first asked for a name and raises
    :class:`NotImplementedError` when a numeral and a constant meet on one name. Translate
    every formula of a problem through ONE environment (``to_z3(env)``) and the refusal
    covers the whole problem, not only one formula.
    """

    def __init__(self, variables_apart: bool = True):
        """Initialise empty symbol, function, and predicate tables."""
        self.variables_apart = variables_apart
        self.symbols: Dict[str, z3.ExprRef] = {}
        self.variables: Dict[str, z3.ExprRef] = {}
        self.funcs: Dict[Tuple[str, int], z3.FuncDeclRef] = {}
        self.preds: Dict[Tuple[str, int], z3.FuncDeclRef] = {}
        # name -> "numeral" / "name": which kind of node asked for the symbol first
        self._claims: Dict[str, str] = {}

    def copy(self) -> "Z3Env":
        """An independent environment that knows everything this one knows."""
        other = Z3Env(self.variables_apart)
        other.symbols.update(self.symbols)
        other.variables.update(self.variables)
        other.funcs.update(self.funcs)
        other.preds.update(self.preds)
        other._claims.update(self._claims)
        return other

    def _claim(self, name: str, kind: str) -> None:
        """Record that ``kind`` (``"numeral"`` or ``"name"``) uses the symbol ``name``; refuse a mixture."""
        seen = self._claims.setdefault(name, kind)
        if seen != kind:
            numeral_constant_clash(name)

    def get_symbol(self, name: str, numeral: bool = False) -> z3.ExprRef:
        """Get or create the Z3 constant of the constant (or numeral) ``name``.

        ``numeral=True`` is the call of :class:`Number`, whose symbol is named by the text of
        its value; it is refused (``NotImplementedError``) when a constant of the same name was
        met, and the other way round. A variable is not asked for here (:meth:`get_variable`).
        """
        self._claim(name, "numeral" if numeral else "name")
        if name not in self.symbols:
            check_z3_name(name)
            self.symbols[name] = z3.Const(z3_constant_name(name), _SORT)
        return self.symbols[name]

    def get_variable(self, name: str) -> z3.ExprRef:
        """Get or create the Z3 constant that stands for the variable ``name``.

        A symbol of its own, apart from the constant of the same name (see the class
        docstring), so a quantifier over it never captures that constant.
        """
        if not self.variables_apart:
            return self.get_symbol(name)
        if name not in self.variables:
            check_z3_name(name)
            self.variables[name] = z3.Const(z3_variable_name(name), _SORT)
        return self.variables[name]

    def get_func(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted Z3 function of the given arity mapping S^arity -> S.

        Keyed on ``(name, arity)``: one name at two arities is two functions.
        """
        if arity == 0:
            self._claim(name, "name")           # a function of no arguments is a constant
        key = (name, arity)
        if key not in self.funcs:
            check_z3_name(name)
            z3_name = z3_constant_name(name) if arity == 0 else name
            self.funcs[key] = z3.Function(z3_name, *([_SORT] * arity), _SORT)
        return self.funcs[key]

    def get_pred(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted Z3 predicate of the given arity mapping S^arity -> Bool.

        Keyed on ``(name, arity)``: one name at two arities is two predicates.
        """
        key = (name, arity)
        if key not in self.preds:
            check_z3_name(name)
            self.preds[key] = z3.Function(name, *([_SORT] * arity), z3.BoolSort())
        return self.preds[key]


# =========================
# Base Node
# =========================

class Node:
    """Base class for all AST nodes."""

    def __init_subclass__(cls, **kwargs):
        """Guard the new class's ``to_tptp`` (see :meth:`to_tptp`).

        Whatever ``to_tptp`` the class resolves to, its own or one inherited
        from a mixin, is replaced by the single-formula collision guard of
        :mod:`unicode_logic_kit.fol._tptp_symbols`. This is what covers every
        node family without each one being edited, and a family added later
        without anyone remembering to ask.
        """
        super().__init_subclass__(**kwargs)
        _guard_to_tptp(cls)

    def _tptp_symbol(self):
        """The name this node itself writes into TPTP text, or ``None``.

        ``(resolver, kit name)``: the kit name in the AST and the module-level
        function (:func:`_predicate_symbol`, :func:`_function_symbol`,
        :func:`_constant_symbol`) that turns it into ``(namespace, word, kind)``,
        the identifier :meth:`to_tptp` writes for it. Only a node that writes a
        NAME, a numeral or a variable overrides this (:class:`Atom`,
        :class:`Function`, :class:`Constant`, :class:`Measure`, ``SortedConstant``,
        :class:`Number`, :class:`Variable`); a node that LOWERS to others
        (``SortedQuantifier`` writes the guard predicate of its sort, a ``Count``
        its witnesses) names nothing itself and is seen through the nodes it is
        rendered as. The single-formula guard and the
        problem writers' collision check both read it, which is why they cannot
        disagree about what a node writes. It only NAMES the symbol (it runs once
        per rendered node); the fold runs once per distinct name, when the symbols
        are checked.
        """
        return None

    def to_dict(self) -> dict:
        """Serialise this node to a JSON-compatible dictionary."""
        raise NotImplementedError

    def to_z3(self, env: Z3Env = None) -> z3.ExprRef:
        """Translate this node into a Z3 expression using the given environment."""
        raise NotImplementedError

    def to_prover9(self) -> str:
        """Render this node as a Prover9-syntax string.

        **What it sees.** The OUTERMOST call of a node that has a binder in it sees the whole
        node and writes text that means it: a binder that sits inside the scope of a binder of
        its own name (the free variables of the node count: Prover9 closes a formula
        universally) is renamed to a fresh variable, because LADR would rename it itself, to
        ``x0``, ``x1``, ... , and a constant of that spelling would then be bound by it; the
        witnesses of a counting quantifier are fresh against every name of the node, of every
        kind, compared case-folded (Prover9 writes a variable in upper case, so ``x0`` and
        ``X0`` are one variable there); and sorted nodes are lowered first. The problem writer
        makes the same preparation of every formula of a problem, with the same functions.

        **What it cannot see.** It renders ONE node and has no whole-problem view.
        A variable is written as the upper-case of its name, so two variables that
        differ only in case are one variable in the text unless a binder is renamed:
        a binder inside the scope of another is (``∀x ∃X R(x, X)`` is written
        ``(all X (exists X0 R(X, X0)))``). What no renaming of a binder repairs is
        refused by name instead of written as one variable: an occurrence that a
        binder of another spelling encloses (a free ``x`` inside ``∀X``), and two free
        variables of one upper-case name (``P(x) ∧ Q(X)``).
        :func:`unicode_logic_kit.atp.prover9_entailment
        .generate_prover9_input_with_mapping` checks every formula of a problem for
        every such pair, harmless ones included, and refuses it by name (the check
        :meth:`to_tptp` makes on its own, from :mod:`unicode_logic_kit.fol._tptp_symbols`);
        build a problem with it, never by joining ``to_prover9()`` strings. A constant
        or a propositional atom that
        Prover9 would read as a variable (a name that begins with an upper-case
        letter or an underscore) is written in double quotes, which Prover9 never
        reads as a variable (see :meth:`Constant.to_prover9`); the writer renames
        such a symbol instead and records the rename. For the same reason it cannot
        see that one name is used for two symbols: a predicate of two arities, or one
        word as a predicate and as a constant, is ONE symbol to Prover9, which
        refuses the file, and the writer gives the later symbol a name of its own.
        A name that is no word Prover9 reads as one symbol (a space, a non-ASCII
        letter, a ``$``-word) is refused by name; the writer renames it. A numeral
        that is not a digit string (``2.5``, ``-1``) is written in double quotes.
        """
        raise NotImplementedError

    def to_tptp(self) -> str:
        """Render this node as a TPTP-syntax string.

        **One formula, checked.** The OUTERMOST call refuses (``NotImplementedError``,
        naming both kit names and the word they share) when two DISTINCT names
        of one kind inside this one formula would be written as the same TPTP
        identifier. A name is written with its first character folded to
        lower-case, so ``gaseous`` and ``Gaseous`` (two constants), ``Foo`` and
        ``foo`` (two predicates) or ``Bar`` and ``bar`` (two functions) would
        otherwise become one symbol and ``P(gaseous) <-> P(Gaseous)`` would be
        written as a tautology. The check sees every name that reaches the
        text, including those a reduction introduces (the sort guard predicate
        of a ``SortedQuantifier``), and is installed on every node class by
        :meth:`__init_subclass__`; a nested call only records.

        Three more cases are written as one word, and refused the same way: a
        number and a constant spelled like it (``Number(1)`` and ``Constant('1')``
        are both ``1``), an arithmetic or comparison symbol and a symbol written
        like it (``+`` is ``$sum``, so a function named ``$sum`` is the same
        word), and two variables that are one TPTP variable (``x`` and ``X``:
        ``∀x ∃X R(x, X)`` would be written ``![X]: ?[X]: r(X,X)``). A formula that
        binds ``x`` in one place and ``X`` in another, even where they never meet,
        is refused too, rather than analysed for scope.

        A name that is written as something that is not a TPTP word is refused as
        well, never written as it is: an unquoted TPTP name is a lower-case letter
        followed by letters, digits and underscores, so ``has-part``,
        ``2008SummerOlympics``, ``_x`` and a non-ASCII predicate or function name
        (a constant is transliterated, ``θ`` is ``theta``) have no rendering. The
        problem writers rewrite such a name under a legal replacement and return
        the map. A word that starts with ``$`` is one of TPTP's own, and is refused
        as a RESERVED word, with ONE exception: the NULLARY atoms ``$true`` and
        ``$false`` are TPTP's defined propositions (this kit's TPTP reader produces
        them), they are written verbatim and are no symbol of the user's, and
        ``to_z3`` reads them as true and false. A VARIABLE that is written as no
        TPTP variable (``ä`` is written ``Ä``, ``x-1``, ``1x``) is refused by name
        too; the problem writers rename a variable, which is bound, without
        recording anything.

        **What it cannot see, and what is not refused.** It sees ONE formula. A
        problem assembled from several ``to_tptp()`` strings can still merge
        ``gaseous`` in one premise with ``Gaseous`` in another, so build a
        problem with :func:`unicode_logic_kit.atp.generate_tptp_problem_with_mapping`
        (or the TF0 / TFA writers), which check every premise and the
        conclusion together. A predicate and a function/constant that share a
        word (the class ``Agent`` and the role function ``agent``) are NOT
        refused here: the text is unambiguous by position and this kit's reader
        reads it back, but a prover may not, so the writers rename the term side
        and return the map.

        **The asymmetry is deliberate, for this release.** A name TPTP cannot
        spell, or a predicate/term clash, is renamed and recorded in a
        ``TptpNameMap`` by the writers; two LEGAL names of one kind that fold
        together are refused by name, never renamed, here and in the writers
        alike. The same-kind refusal predates the name map and stays so that no
        existing caller silently receives a symbol renamed behind its back.

        Raises:
            NotImplementedError: two symbols written as one word, or a name
                that is not a TPTP word (above), or a construct outside the
                classical first-order fragment (modal, second-order,
                Łukasiewicz, lambda, ...), which names itself.
        """
        raise NotImplementedError

    @staticmethod
    def from_dict(d: dict) -> "Node":
        """Deserialise a node from a dictionary produced by to_dict."""
        t = d["_type"]
        if t not in NODE_CLASSES:
            raise ValueError(f"Unknown type: {t}")
        return NODE_CLASSES[t].from_dict(d)

    _TREE_LABELS = {
        "And": "∧", "Or": "∨", "Xor": "⊕",
        "Implies": "→", "Iff": "↔", "Not": "¬",
        "Contrast": "Ⓒ",
    }

    def _tree_parts(self):
        """Return (label, children) for tree rendering.

        Leaf terms render their value in the label and have no children.
        Atom and Function render the symbol in the label and expose their
        argument nodes. Quantifier shows its type and bound variable.
        Everything else falls back to its dataclass fields, treating any
        Node-valued field as a child.
        """
        cls = type(self).__name__
        if cls in ("Variable", "Constant"):
            return f"{cls}: {self.name}", []
        if cls == "Number":
            return f"Number: {self.value}", []
        if cls == "Atom":
            return f"Atom: {self.predicate}", list(self.args)
        if cls == "Function":
            return f"Function: {self.name}", list(self.args)
        if cls == "Quantifier":
            return f"{self.type} {self.variable.name}", [self.formula]

        label = self._TREE_LABELS.get(cls, cls)
        children = []
        for f in fields(self):
            value = getattr(self, f.name)
            if isinstance(value, Node):
                children.append(value)
            elif isinstance(value, (list, tuple)):
                children.extend(c for c in value if isinstance(c, Node))
        return label, children

    def to_unicode_str(self) -> str:
        """Render this node back to a Unicode formula string.

        The result, re-parsed in the matching MSFLParser mode, yields a
        structurally equal AST (parser round-trip): ``parse(n.to_unicode_str())
        == n`` -- for every node that has a text form (see the last paragraph:
        a node that mixes sorted and unsorted occurrences has none). For the classical FOL fragment (``∀ ∃ ¬ ∧ ∨ → ↔ ⊕`` and
        predicates over constants/variables — no lambda, no modal, no
        second-order) this is the B2 roundtrip guarantee, exercised
        example-by-example in ``tests/test_to_unicode_str.py`` and, starting
        from arbitrary hand-built nodes rather than parser output, in
        ``tests/test_fol_fragment_roundtrip_b2.py`` (hand-picked
        parenthesisation edge cases plus a seeded randomized property
        search). This is part of this method's STABLE PUBLIC API contract —
        see the module docstring of ``fol/nodes.py``. The renderer lives in
        _msfl_nodes.py (imported lazily to avoid a circular import) because it
        dispatches over both the FOL nodes here and the MSFL/lambda nodes there.

        **A node that mixes sorted and unsorted occurrences has no text form.**
        The many-sorted text grammar is all-sorted or all-unsorted: a sorted
        quantifier over an unsorted one (``∀x:A ∃y P(x, y)``), a constant written
        ``carl:A`` in one place and plain ``carl`` in another, or an unsorted
        quantifier around a sorted constant prints text that every parser refuses
        (``NamingError``), in every mode. The refusal is loud: such text is never
        read back as a different formula. The node itself is a legitimate formula
        (``c:S`` and plain ``c`` are one constant in the kit's semantics, and an
        unsorted variable ranges over the whole universe), so decide, translate
        and export it as a node, or write the sort on every occurrence (or on none)
        before printing it.
        """
        from ._msfl_nodes import _uni
        return _uni(self)

    def to_latex(self) -> str:
        """Render this node as a LaTeX math-mode string (no surrounding $…$).

        Uses the same precedence-driven parenthesisation as to_unicode_str.
        Symbol/function/predicate names are emitted verbatim (no \\mathrm
        wrapping). The renderer lives in _msfl_nodes.py (imported lazily) so it
        can dispatch over both FOL and MSFL/lambda nodes.
        """
        from ._msfl_nodes import _latex
        return _latex(self)

    def to_smtlib(self) -> str:
        """Render this node as a standalone SMT-LIB2 problem (one ``(assert ...)``).

        A one-line delegation to :func:`unicode_logic_kit.atp.z3_input.to_smtlib`
        with no premises — the general, multi-premise/sanitisation-correct
        exporter promoted from :class:`~unicode_logic_kit.atp.cvc5_backend
        .Cvc5Backend`'s own already-proven translation; see that function's
        docstring for what "sanitisation-correct" buys over a naive
        ``to_z3()`` + ``z3.Solver.to_smt2()`` combination. Imported lazily
        (like :meth:`to_latex`) because ``atp.z3_input`` imports from this
        module's own package at load time — mirrors how :meth:`to_z3`
        already crosses the fol/atp module boundary, just one hop further.

        Raises:
            NotImplementedError: this node (or a descendant) uses a construct
                with no first-order SMT-LIB2 encoding — the same refusal
                :meth:`to_z3` raises for it.
        """
        from ..atp.z3_input import to_smtlib as _to_smtlib
        return _to_smtlib(self)

    def _repr_latex_(self) -> Optional[str]:
        """Jupyter/IPython rich-display hook: LaTeX math-mode rendering.

        Wraps :meth:`to_latex` in ``$$...$$`` (display math). MUST NOT raise —
        IPython's formatter machinery treats an exception from a ``_repr_*_``
        method as a hard failure of that cell's output, not as "fall back to
        the next formatter". :meth:`to_latex` refuses loudly (``TypeError`` /
        ``NotImplementedError``) for a node it cannot render, e.g. a
        third-party ``Node`` subclass the LaTeX dispatcher has never heard of;
        here that refusal is swallowed and reported as "no LaTeX
        representation" (``None``) instead, so IPython falls back to the
        plain ``repr()`` of the node rather than showing a traceback in a
        notebook cell.
        """
        try:
            return f"$${self.to_latex()}$$"
        except Exception:
            return None

    def tree_str(self) -> str:
        """Render the AST as a multi-line ASCII tree using ├──/└── connectors."""
        label, children = self._tree_parts()
        lines = [label]
        for i, child in enumerate(children):
            last = i == len(children) - 1
            branch = "└── " if last else "├── "
            prefix = "    " if last else "│   "
            sub = child.tree_str().split("\n")
            lines.append(branch + sub[0])
            lines.extend(prefix + s for s in sub[1:])
        return "\n".join(lines)

    def to_msfol(self) -> "Node":
        """Lower Łukasiewicz operators to classical counterparts; recurse into children.

        Classical and sort-annotated nodes return a structurally equal copy with
        children recursed. Fuzzy operator subclasses override this to substitute
        the corresponding classical node type.
        """
        return self.map_children(lambda c: c.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        """Replace sorted nodes with plain FOL constructs; collect sort-membership atoms.

        Classical nodes return a structurally equal copy with children recursed.
        SortedQuantifier and SortedConstant override this with their specific rules.
        Fuzzy operator subclasses override to raise RuntimeError — they must be
        eliminated by to_msfol() before _relativize() is called.
        """
        return self.map_children(lambda c: c._relativize(facts))

    # ---------------------------------------------------------------
    # Traversal / inspection API
    # ---------------------------------------------------------------

    def _child_nodes(self) -> List["Node"]:
        """Return the immediate Node-valued children, in declaration order.

        Covers both single Node fields and lists of Nodes. Quantifier exposes
        its bound variable here (it is a Node); for a rendering-oriented child
        view see _tree_parts.
        """
        result: List["Node"] = []
        for f in fields(self):
            val = getattr(self, f.name)
            if isinstance(val, Node):
                result.append(val)
            elif isinstance(val, (list, tuple)):
                result.extend(c for c in val if isinstance(c, Node))
        return result

    def map_children(self, fn) -> "Node":
        """Rebuild this node with ``fn`` applied to each immediate Node child.

        The single point of structural recursion. Each dataclass field is
        handled by kind: a Node field becomes ``fn(value)``; a list/tuple field
        has ``fn`` mapped over its Node elements (non-Node elements pass
        through, container kind preserved); any other field is copied verbatim.
        The node type and field order are preserved.

        Binders (Lambda, Quantifier, SortedQuantifier) carry their bound
        variable as a plain Node field, so ``fn`` is applied to it too; callers
        that must treat a binder's scope specially should handle that case
        explicitly before delegating here. This is the shared engine behind the
        purely structural recursions (to_msfol, _relativize, beta/eta reduction,
        scope resolution, …), so a new structural node type is handled
        automatically without touching each traversal.
        """
        new_kwargs = {}
        for f in fields(self):
            val = getattr(self, f.name)
            if isinstance(val, Node):
                new_kwargs[f.name] = fn(val)
            elif isinstance(val, (list, tuple)):
                new_kwargs[f.name] = type(val)(
                    fn(c) if isinstance(c, Node) else c for c in val
                )
            else:
                new_kwargs[f.name] = val
        return type(self)(**new_kwargs)

    def walk(self):
        """Yield this node and every descendant in pre-order (depth-first).

        A node comes before its children and the children come left to right, in the
        order of ``Node._child_nodes``. The traversal keeps its own stack, so a formula
        nested thousands of levels deep is walked as readily as a shallow one: it does
        not depend on the interpreter's recursion limit.
        """
        stack = [self]
        while stack:
            node = stack.pop()
            yield node
            stack.extend(reversed(node._child_nodes()))

    def subformulas(self):
        """Yield every sub-node that is a formula (i.e. not an atomic term).

        Terms (Variable, Constant, Number, Function, SortedConstant, LambdaVar)
        are excluded; everything else reachable is returned in pre-order.
        """
        return [n for n in self.walk() if type(n).__name__ not in _TERM_NAMES]

    def atoms(self):
        """Return all Atom nodes in pre-order (duplicates kept; comparisons included)."""
        return [n for n in self.walk() if isinstance(n, Atom)]

    def variables(self):
        """Return the set of logical Variable nodes occurring anywhere (free and bound)."""
        return {n for n in self.walk() if isinstance(n, Variable)}

    def count(self, cls=None) -> int:
        """Count nodes in the tree; if cls is given, only nodes of that type."""
        return sum(1 for n in self.walk() if cls is None or isinstance(n, cls))

    def depth(self) -> int:
        """Return the height of the tree; a leaf node has depth 1."""
        children = self._child_nodes()
        return 1 + max((c.depth() for c in children), default=0)

    def to_dot(self) -> str:
        """Render the AST as a Graphviz DOT digraph string.

        Uses the same label/child view as tree_str (the bound variable of a
        quantifier is folded into its node label, not shown as a child), so the
        graph mirrors the ASCII tree. No external dependency: returns the source.
        """
        lines = ["digraph AST {", "  node [shape=box];"]
        counter = [0]

        def emit(node: "Node") -> int:
            my_id = counter[0]
            counter[0] += 1
            label, children = node._tree_parts()
            safe = label.replace("\\", "\\\\").replace('"', '\\"')
            lines.append(f'  n{my_id} [label="{safe}"];')
            for child in children:
                child_id = emit(child)
                lines.append(f"  n{my_id} -> n{child_id};")
            return my_id

        emit(self)
        lines.append("}")
        return "\n".join(lines)


# ``__init_subclass__`` guards every SUBCLASS; the base's own ``to_tptp`` (it
# raises, and a subclass without one inherits it) is guarded here so that every
# node class, ``Node`` included, answers ``is_guarded`` the same way.
_guard_to_tptp(Node)


# =========================
# Public tree editing (path-addressed replacement) and PATH CONVENTION
# =========================
#
# replace_at is the PUBLIC, node-type-generic counterpart to the private
# atp.resolution._replace_at (a term-only helper restricted to Atom/Function
# argument positions — see replace_at's own docstring for the exact
# difference). It is built on the same structural machinery Node.map_children
# already uses for every other whole-tree rewrite in this codebase (to_msfol,
# _relativize, beta/eta reduction, scope resolution, …).
#
# PATH CONVENTION — the one thing traversal (fol.spans.traverse), span lookup
# (fol.spans.SpanMap) and replace_at/node_at must all agree on (spec item
# A2). A path is a tuple of non-negative ints, addressing a node relative to
# some root: () addresses the root itself; (i, *rest) addresses rest inside
# the root's i-th PATH CHILD. _path_children(node) IS Node._child_nodes()
# (the SAME child order Node.walk/.map_children/.count/.depth already use)
# for every node type EXCEPT Quantifier, whose bound `variable` is excluded:
# a Quantifier's ONLY path child is its `formula`, at index 0.
#
# The exclusion is deliberate and spec-driven (fol.spans's module docstring,
# "WHY THE BOUND VARIABLE IS EXCLUDED"): a quantifier's HEAD span already
# covers its symbol together with its bound variable as one occurrence
# ("∀ x"), so exposing the variable AGAIN as a separately path-addressable
# child would double-count that one piece of source text. It mirrors how
# Node._tree_parts()/to_dot already fold the bound variable into the node's
# *label* rather than its *children* — here it is folded into the node's
# *head span* rather than its *path children*, same idea, different API.
# Scoped to Quantifier alone (not every binder — Count, Cardinality,
# SortedQuantifier, Lambda, … keep the default, unexcluded view) because
# Quantifier is the one binder the span layer's target FOL fragment covers;
# widening the exclusion to every binder is a separate decision left to
# whichever future change extends spans past that fragment.

def _path_children(node: "Node") -> List["Node"]:
    """The path-addressable children of ``node``, in path-index order — see
    the PATH CONVENTION comment above."""
    if isinstance(node, Quantifier):
        return [node.formula]
    return node._child_nodes()


def node_at(root: "Node", path: Tuple[int, ...]) -> "Node":
    """Return the node ``path`` addresses in ``root``'s tree (see the PATH
    CONVENTION comment above ``_path_children``).

    Raises ``IndexError`` if ``path`` does not address a node in this tree —
    an index out of range at some prefix of ``path`` — never returns a guess.
    """
    node = root
    for depth, idx in enumerate(path):
        children = _path_children(node)
        if not isinstance(idx, int) or not (0 <= idx < len(children)):
            raise IndexError(
                f"node_at: path {path!r} is invalid at position {depth} "
                f"(index {idx!r}) — a {type(node).__name__} node has "
                f"{len(children)} path child(ren) there."
            )
        node = children[idx]
    return node


def _replace_child_at(node: "Node", index: int, new_child: "Node") -> "Node":
    """Rebuild ``node`` with its ``index``-th PATH child (see
    ``_path_children``) replaced by ``new_child``; every other field is
    copied verbatim and every other Node child is passed through BY
    REFERENCE — the exact same object, not a copy.

    A :class:`Quantifier` (whose one path child is its ``formula``, NOT
    ``_child_nodes()``'s ``[variable, formula]``) is rebuilt directly via
    ``Quantifier(node.type, node.variable, new_child)`` rather than through
    ``map_children`` — ``map_children`` is defined over ``_child_nodes()``
    and applies its function to the bound variable too (see its own
    docstring), which is exactly the field this path convention excludes.
    Every other node type's path children ARE ``_child_nodes()``, so
    ``map_children`` (with a counting closure that substitutes only the
    targeted slot; every other child call returns its argument unchanged,
    passed through by reference) is both correct and guaranteed consistent
    with ``_path_children``'s own indexing — same field walk, not a separate
    reimplementation that could drift out of sync with it.
    """
    if isinstance(node, Quantifier):
        if index != 0:
            raise IndexError(
                f"replace_at: Quantifier has exactly one path child (its "
                f"formula, index 0); got index {index}")
        return Quantifier(node.type, node.variable, new_child)

    seen = 0

    def fn(child):
        nonlocal seen
        this_index = seen
        seen += 1
        return new_child if this_index == index else child

    return node.map_children(fn)


def replace_at(root: "Node", path: Tuple[int, ...], new_node: "Node") -> "Node":
    """Return a new tree: ``root`` with the subtree addressed by ``path``
    replaced by ``new_node``. ``root`` and every node reachable from it are
    left untouched — nodes are frozen dataclasses, so in-place mutation is
    not even possible; ``replace_at`` only ever builds new node instances
    along the spine from the root down to the replaced subtree.

    ``path`` uses the PATH CONVENTION documented above ``_path_children``
    (the same one :func:`node_at` and
    :func:`unicode_logic_kit.fol.spans.traverse`/
    :class:`~unicode_logic_kit.fol.spans.SpanMap` use) — in particular, a
    :class:`Quantifier`'s bound variable is NOT reachable via any
    ``replace_at`` path; its only path child is its ``formula``, at index 0.

    STABILITY GUARANTEE (B1). For any path ``q`` that does not run through
    the replaced subtree — ``q`` is not ``path``, not a prefix of ``path``
    (an ancestor), and not extended by ``path`` (a descendant) — the node
    reachable via ``q`` in the result is the SAME object (``is``) as the
    node reachable via ``q`` in the original tree, because every node off
    the root-to-``path`` spine is passed through by reference at each
    rebuilt ancestor (see :func:`_replace_child_at`). Only the spine itself
    — ``root`` and every proper prefix of ``path`` — is rebuilt (new
    objects, since each now contains the replacement somewhere below it);
    everything else in the tree is untouched.

    Raises ``IndexError`` if any prefix of ``path`` runs off the tree — an
    index that is out of range for the node's path children at that depth
    (this also covers handing a non-empty path to a leaf node, whose path
    children are always empty).
    """
    path = tuple(path)

    def rec(node: "Node", depth: int) -> "Node":
        if depth == len(path):
            return new_node
        idx = path[depth]
        children = _path_children(node)
        if not isinstance(idx, int) or not (0 <= idx < len(children)):
            raise IndexError(
                f"replace_at: path {path!r} is invalid at position {depth} "
                f"(index {idx!r}) — a {type(node).__name__} node has "
                f"{len(children)} path child(ren) there."
            )
        new_child = rec(children[idx], depth + 1)
        return _replace_child_at(node, idx, new_child)

    return rec(root, 0)


# Term node class names — used by Node.subformulas to exclude atomic terms.
# Measure and Cardinality are term-valued (they occur in argument position and
# are compared with </>); Cardinality additionally carries a formula child, which
# Node.walk still descends into, so its φ is still reported among subformulas.
_TERM_NAMES = frozenset({
    "Variable", "Constant", "Number", "Function", "SortedConstant", "LambdaVar",
    "Measure", "Cardinality",
})


# =========================
# Term Nodes
# =========================

@dataclass(frozen=True)
class Variable(Node):
    """A logical variable, represented by a single lowercase letter in the grammar."""

    name: str

    def to_dict(self):
        """Serialise to dict with type tag and variable name."""
        return {"_type": "Variable", "name": self.name}

    @staticmethod
    def from_dict(d):
        """Deserialise a Variable from a dict produced by to_dict."""
        return Variable(d["name"])

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 constant in the uninterpreted sort S.

        A variable is a symbol of its own, apart from a constant of the same name (see
        :class:`Z3Env`): the quantifier that binds ``x`` binds no constant named ``x``.
        """
        return (env or Z3Env()).get_variable(self.name)

    def to_prover9(self) -> str:
        """Render the variable name in uppercase.

        The Prover9 driver enables ``set(prolog_style_variables)``, under which a
        symbol that no quantifier binds is a variable only if it begins with an
        uppercase letter (an underscore does not make one: measured on Prover9
        2026-8A, ``_x`` is a constant with the flag and without it). Grammar variable
        names are always lowercase, so they are uppercased here; constants and
        predicate/function names stay as-is.

        A name with a non-ASCII character is refused: Prover9 reads ASCII only,
        and upper-casing can give the SAME text for two different variables
        (``ı`` and ``i`` both print as ``I``, ``ſ`` and ``s`` as ``S``, the
        ligatures ``ﬅ`` and ``ﬆ`` as ``ST``), which would silently merge them. A name that
        is no word either (``x-1``, ``1x``, ``x'``, an empty name) is refused as well: written
        bare, Prover9 reads an operator or another symbol in it, and the kit's own reader
        could not read the text back.
        """
        if not self.name.isascii():
            raise NotImplementedError(
                f"to_prover9: variable {self.name!r} has a non-ASCII character. "
                f"Prover9 reads ASCII only, and upper-casing {self.name!r} gives "
                f"{self.name.upper()!r}, which is either text Prover9 cannot read "
                f"or the same text as another variable (ı and i both print as 'I'). "
                f"Rename the variable to an ASCII letter followed by digits "
                f"(x, y1) before exporting.")
        if not _PROVER9_IDENTIFIER_RE.fullmatch(self.name):
            raise NotImplementedError(
                f"to_prover9: variable {self.name!r} is no word Prover9 reads as one symbol: "
                f"it is written as {self.name.upper()!r}, and only letters, digits and "
                f"underscores, not beginning with a digit, make a word (a '-', a '.', a quote "
                f"or a leading digit is read as an operator or as another symbol). "
                f"Rename the variable to an ASCII letter followed by digits "
                f"(x, y1) before exporting.")
        return self.name.upper()

    def to_tptp(self) -> str:
        """Render variable in TPTP syntax. TPTP requires variables to be uppercase; single lowercase letters are capitalized.

        The outermost :meth:`Node.to_tptp` call refuses a variable whose upper-case
        is no TPTP variable (``ä``, ``x-1``, ``1x``); the problem writers rename it."""
        return self.name.upper()

    def _tptp_symbol(self):
        """The TPTP variable :meth:`to_tptp` writes: the upper-case of the name, so ``x`` and ``X`` are one."""
        return (_variable_symbol, self.name)


# --------------------------------------------------------------------------- #
# Reversible ASCII transliteration for non-ASCII constant names.
#
# A constant may carry a non-ASCII (Greek) letter — e.g. a threshold ``θ`` — which
# the Kripke evaluator and Z3 handle directly (Z3 symbol names are arbitrary
# strings). The *text*-based first-order back-ends (Prover9 / TPTP) accept only
# ASCII identifiers, so on export each Greek letter (except the reserved operator
# glyphs λ / μ) maps to its conventional ASCII name and any other non-ASCII
# character uses a reversible ``uXXXX`` codepoint escape — a name is never emitted
# raw. Deterministic; invertible via :func:`constant_name_from_ascii` (exactly for a
# single-symbol constant, the realistic case).
# --------------------------------------------------------------------------- #

_GREEK_CONST_TO_ASCII = {
    "α": "alpha", "β": "beta", "γ": "gamma", "δ": "delta", "ε": "epsilon",
    "ζ": "zeta", "η": "eta", "θ": "theta", "ι": "iota", "κ": "kappa",
    "ν": "nu", "ξ": "xi", "ο": "omicron", "π": "pi", "ρ": "rho",
    "σ": "sigma", "τ": "tau", "υ": "upsilon", "φ": "phi", "χ": "chi",
    "ψ": "psi", "ω": "omega",
}
_ASCII_TO_GREEK_CONST = {v: k for k, v in _GREEK_CONST_TO_ASCII.items()}
_UESC_RE = re.compile(r"u([0-9a-f]{4})")


def constant_name_to_ascii(name: str) -> str:
    """Transliterate a (possibly non-ASCII) constant name to a valid ASCII identifier.

    ASCII characters pass through; a Greek letter maps to its conventional name
    (``θ`` → ``theta``); any other non-ASCII character becomes a reversible ``uXXXX``
    codepoint escape. Deterministic; inverse is :func:`constant_name_from_ascii`.
    """
    out = []
    for ch in name:
        if ch.isascii():
            out.append(ch)
        elif ch in _GREEK_CONST_TO_ASCII:
            out.append(_GREEK_CONST_TO_ASCII[ch])
        else:
            out.append("u%04x" % ord(ch))
    return "".join(out)


def constant_name_from_ascii(s: str) -> str:
    """Inverse of :func:`constant_name_to_ascii` for a single transliterated symbol.

    Recovers the original character when ``s`` is exactly one Greek name (``theta`` →
    ``θ``) or a ``uXXXX`` escape; otherwise returns ``s`` unchanged. Multi-symbol
    concatenations are deterministic forward but not uniquely decodable, so only
    single-symbol constants (the realistic case) are guaranteed to round-trip.
    """
    if s in _ASCII_TO_GREEK_CONST:
        return _ASCII_TO_GREEK_CONST[s]
    m = _UESC_RE.fullmatch(s)
    if m:
        return chr(int(m.group(1), 16))
    return s


def _prover9_reads_as_variable(token: str) -> bool:
    """Whether Prover9, under ``set(prolog_style_variables)``, reads the symbol
    ``token`` in TERM position as a VARIABLE rather than as a constant.

    Prover9's own rule (LADR ``ladr/symbols.c``, ``variable_name``): with that
    flag set, a symbol is a variable iff its first character is ``A``..``Z``
    (the manual: "If this flag is set, variables in clauses start with (upper
    case) 'A' through 'Z'"). It applies to every ARITY-0 symbol in term
    position (``set_vars_recurse`` converts a ``CONSTANT`` term), so a constant
    is affected; a function or predicate WITH arguments is not (the symbol is
    not a constant term, only its arguments are examined). The LADR source reads
    only ``A``..``Z``: measured on Prover9 2026-8A, ``_x`` is a constant with the
    flag and without it, and this kit's own Prover9 reader
    (:mod:`~unicode_logic_kit.fol.prover9_input`) reads it as one too. A leading
    underscore is nevertheless treated like a capital here, because the Prolog
    convention reads it as a variable and a text that another reader may take
    for a variable must not carry the name bare; the cost is a rename or a pair of
    quotes that Prover9 did not need.
    """
    first = token[:1]
    return first == "_" or ("A" <= first <= "Z")


_PROVER9_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

#: A name Prover9 reads as ONE symbol when it is written bare: ASCII letters,
#: digits and underscores (a digit-leading word is one symbol too: ``2nd(X)`` is
#: read, measured on Prover9 2026-8A).
_PROVER9_WORD_RE = re.compile(r"[A-Za-z0-9_]+")

#: The two words LADR reads as quantifiers. As a predicate or a function applied to a
#: variable at the start of an operand, ``exists(X) & ...`` is read as ``exists X``
#: followed by a stray ``&`` (measured on Prover9 2026-8A: Prover9 echoes
#: ``(exists W exists W &(Q(c) & R(c)))`` and ends with ``symbols used with multiple
#: arities: &/1, &/2``). A double-quoted symbol is never a keyword, so these are written
#: in double quotes at every arity; the problem writer renames them instead.
_PROVER9_QUANTIFIERS = frozenset({"all", "exists"})

#: Symbols, by name AND arity, that Prover9 or this kit's own reader of Prover9 files reads as
#: something other than an ordinary symbol (measured on Prover9 2026-8A):
#:
#: * ``if`` at three arguments: LADR reads the first argument as a FORMULA, so
#:   ``(all W if(W, a, a))`` is refused ("cannot be used as atomic formulas, because they are
#:   variables: W") and ``if(a, b, c)`` makes ``a`` a relation symbol, which a constant ``a``
#:   elsewhere in the file contradicts;
#: * ``end_of_list`` with no argument: inside a ``formulas(...)`` list the bare word ends the
#:   list, so a proposition of that name is "Unrecognized command or list";
#: * ``formulas`` at one argument: Prover9 reads ``formulas(alpha)`` in a list as an atom, but a
#:   file reader that takes it for the header of a nested list cannot read the text back.
#:
#: A double-quoted symbol is a symbol of its own that none of this applies to, so a single
#: renderer writes these in double quotes; the problem writer renames them instead.
_PROVER9_RESERVED_SYMBOLS = frozenset({("if", 3), ("end_of_list", 0), ("formulas", 1)})


def _prover9_arity_zero_symbol(token: str) -> Optional[str]:
    """The text that makes Prover9 read the arity-0 symbol ``token`` as itself: a
    constant in term position, a proposition in formula position.

    A name that Prover9 would not read as a variable
    (:func:`_prover9_reads_as_variable`) is written as it is. One that it would
    is written in double quotes. LADR stores a double-quoted symbol WITH its
    quote characters, so the first character it tests for the variable rule is
    the quote, in every variable style; ``"Gaseous"`` is a constant and
    ``"Rain"`` a proposition, each distinct from the bare word of the same
    letters (measured on Prover9 2026-8A, with and without
    ``prolog_style_variables``). The quantifier words ``all`` and ``exists`` are
    written in double quotes too (:data:`_PROVER9_QUANTIFIERS`), and so is a word that is
    reserved at no argument (:data:`_PROVER9_RESERVED_SYMBOLS`). LADR has no escape
    inside quotes, so a name can be quoted only when it is a plain word (ASCII
    letters, digits and underscore, which excludes the quote itself). ``None`` says
    the name is no such word (it holds a space, a punctuation mark, a non-ASCII
    letter, or nothing at all): it can be written neither bare nor quoted, and the
    caller refuses it by name (:func:`_prover9_name_refusal`).
    """
    if _PROVER9_WORD_RE.fullmatch(token) is None:
        return None
    if (token in _PROVER9_QUANTIFIERS or (token, 0) in _PROVER9_RESERVED_SYMBOLS
            or _prover9_reads_as_variable(token)):
        return '"' + token + '"'
    return token


def _prover9_name_refusal(what: str, name: str, written: Optional[str] = None
                          ) -> NotImplementedError:
    """The refusal for a symbol name that can be written neither bare nor in quotes.

    ``what`` says which symbol (``"the predicate"``, ``"the constant"``), ``name``
    is the kit name and ``written`` the text it was reduced to when that differs
    (a constant is transliterated first). A name that begins with ``$`` gets the
    reason that is its own: Prover9 keeps those words for itself.
    """
    if name.startswith("$"):
        return NotImplementedError(
            f"to_prover9: {what} {name!r} is a '$'-word. Prover9 keeps the words that begin "
            f"with '$' for itself (its truth constants are $T and $F), so a symbol spelled "
            f"like that is not a name of the user's, and the text would say something else; "
            f"the kit writes only the nullary atoms $true and $false, as $T and $F. Rename "
            f"the symbol before exporting it.")
    shown = f" (written {written!r})" if written is not None and written != name else ""
    return NotImplementedError(
        f"to_prover9: {what} {name!r}{shown} cannot be written for Prover9. Prover9 reads a "
        f"bare word of ASCII letters, digits and underscores as one symbol and a "
        f"double-quoted word as another, and this name is neither: it holds a space, a "
        f"punctuation mark or a non-ASCII letter, or it is empty, so any text for it would "
        f"be read as several symbols or refused. Build the problem with "
        f"unicode_logic_kit.atp.prover9_entailment.generate_prover9_input_with_mapping, which "
        f"writes such a name under an ASCII replacement and returns the map, or rename it.")


def _prover9_word(name: str, what: str, arity: Optional[int] = None) -> str:
    """``name`` as the word of a predicate or function that has ``arity`` arguments, or a
    refusal by name. Such a symbol is never read as a variable, whatever its first
    letter, so only its shape matters; the quantifier words ``all`` and ``exists``, and a
    word reserved at this number of arguments (:data:`_PROVER9_RESERVED_SYMBOLS`), are the
    exception, which are written in double quotes (:data:`_PROVER9_QUANTIFIERS`)."""
    if _PROVER9_WORD_RE.fullmatch(name) is None:
        raise _prover9_name_refusal(what, name)
    if name in _PROVER9_QUANTIFIERS or (name, arity) in _PROVER9_RESERVED_SYMBOLS:
        return '"' + name + '"'
    return name


#: True while the OUTERMOST ``to_prover9`` of a node writes the tree :func:`_prover9_prepared` made of
#: it, and in every call nested below it: such a call writes its node as it is.
_PROVER9_PREPARED: "contextvars.ContextVar[bool]" = contextvars.ContextVar(
    "unicode_logic_kit_prover9_prepared", default=False)


def _prover9_scope_scan(node: "Node") -> Tuple[bool, frozenset]:
    """Whether a binder of ``node`` is read by Prover9 as one that re-binds a name, and the upper-case
    names of the free variables of ``node``. Iterative: it costs no recursion depth.

    A binder re-binds when it sits inside the scope of a binder of its own name, or when a variable of
    its name is free somewhere in the node (Prover9 closes a formula universally, so the closure is a
    binder that every other one sits in). Names are compared as Prover9 reads them, in upper case.
    """
    free: set = set()
    binders: list = []
    rebound = False
    stack: list = [(node, frozenset())]
    while stack:
        current, bound = stack.pop()
        if isinstance(current, Variable):
            if current.name.upper() not in bound:
                free.add(current.name.upper())
        elif isinstance(current, Quantifier):
            name = current.variable.name.upper()
            rebound = rebound or name in bound
            binders.append(name)
            stack.append((current.formula, bound | {name}))
        else:
            stack.extend((child, bound) for child in current._child_nodes())
    return rebound or any(name in free for name in binders), frozenset(free)


def _prover9_merged_variables(node: "Node") -> Optional[Tuple[str, str]]:
    """Two variables of ``node`` that its text would read as ONE, or ``None``. Iterative.

    Prover9 reads a variable by the upper-case of its name, so ``x`` and ``X`` are one variable in the
    text. That is harmless where the two are bound apart (``(all X P(X)) & (all X Q(X))``), and a binder
    inside the scope of another of the same upper-case name is renamed (:func:`_prover9_prepared`). What
    is left, and what no renaming of a binder can repair, is an occurrence that the binder of ITS name
    does not enclose but a binder of the same upper-case name does (``∀X P(x)`` with a free ``x``: the
    text binds it), and two free variables of one upper-case name (``P(x) ∧ Q(X)``: two parameters
    become one). Call it on a tree whose re-bound binders are already renamed.
    """
    free: dict = {}
    stack: list = [(node, {})]
    while stack:
        current, binders = stack.pop()
        if isinstance(current, Variable):
            upper = current.name.upper()
            binder = binders.get(upper)
            if binder is None:
                first = free.setdefault(upper, current.name)
                if first != current.name:
                    return first, current.name
            elif binder != current.name:
                return binder, current.name
        elif isinstance(current, Quantifier):
            stack.append((current.formula, {**binders, current.variable.name.upper(): current.variable.name}))
        else:
            stack.extend((child, binders) for child in current._child_nodes())
    return None


def _prover9_refuse_merged_variables(node: "Node") -> None:
    """Refuse ``node`` by name when two of its variables would be read as one (see
    :func:`_prover9_merged_variables`); the refusal is the one the problem writer makes."""
    pair = _prover9_merged_variables(node)
    if pair is not None:
        _check_variable_names(Atom("variables", tuple(Variable(name) for name in pair)),
                              where="Node.to_prover9", subject="formula", dialect="prover9")


def _prover9_prepared(node: "Node") -> "Node":
    """The tree whose text means what ``node`` means: ``node`` with its binders made safe for Prover9.

    Prover9 reads the names of a text, not the tree, and two things make it read another formula than
    the node whose text it is. LADR renames a variable that a quantifier binds inside the scope of a
    quantifier of the same name, to ``x0``, ``x1``, ... (the first that is no variable in scope), and
    takes a constant of that spelling for it: ``(all W (all W P(W, x0)))`` is clausified to
    ``P(A, A)``. And a counting witness is a name minted for the text: Prover9 writes a variable in
    upper case, so a witness ``x0`` next to a variable ``X0`` is ONE variable.

    This is the preparation the problem writer makes of every formula of a problem, with the same two
    functions (``_lower_for_prover9`` and ``_rename_rebound_binders`` of
    ``unicode_logic_kit.atp.prover9_entailment``): sorted nodes are lowered, the witnesses of a counting
    quantifier are fresh against every name of the whole node, of every kind, compared case-folded, and
    a binder that re-binds a name (see :func:`_prover9_scope_scan`) is renamed to a fresh variable. A
    node that needs none of this is returned as it is, so a formula that holds no re-bound binder and
    no counting quantifier is written exactly as deep as it always was, and so is a node that holds a
    Lukasiewicz connective (the connective refuses itself when it is written).

    Two variables that differ only in case and that no renaming of a binder can tell apart are refused by
    name (:func:`_prover9_merged_variables`), as the problem writer refuses them.

    Raises:
        NotImplementedError: two variables of ``node`` would be written as one.
    """
    from ..atp.prover9_entailment import _LUKASIEWICZ_NODES, _lower_for_prover9, _rename_rebound_binders
    nodes = list(node.walk())
    names = {n.name for n in nodes if isinstance(n, Variable)}
    merged = len({name.upper() for name in names}) < len(names)
    if not any(getattr(n, "variable", None) is not None for n in nodes):
        if merged:
            _prover9_refuse_merged_variables(node)
        return node
    if any(isinstance(n, _LUKASIEWICZ_NODES) for n in nodes):
        return node
    if any(isinstance(n, Variable) and not n.name.isascii() for n in nodes):
        return node          # a variable that Prover9 cannot read is refused by name when it is written
    lowering = any(isinstance(n, Count) or type(n).__name__ in ("SortedQuantifier", "SortedCount")
                   for n in nodes)
    if not lowering and not _prover9_scope_scan(node)[0]:
        if merged:
            _prover9_refuse_merged_variables(node)
        return node
    avoid = set(_identifiers.symbol_names(node, fold=str.casefold))
    lowered = node
    if lowering:
        try:
            lowered = _lower_for_prover9(node, avoid)
        except NotImplementedError:
            return node      # the node that cannot be written says so itself, when it is written
    rebinds, free = _prover9_scope_scan(lowered)
    prepared = _rename_rebound_binders(lowered, avoid, free) if rebinds else lowered
    if merged:
        _prover9_refuse_merged_variables(prepared)
    return prepared


def _prover9_write_outermost(node: "Node") -> str:
    """Write the text of ``node`` from the tree :func:`_prover9_prepared` makes of it."""
    prepared = _prover9_prepared(node)
    token = _PROVER9_PREPARED.set(True)
    try:
        return prepared.to_prover9()
    finally:
        _PROVER9_PREPARED.reset(token)


class _Prover9Entry:
    """The descriptor :func:`_prover9_outermost` puts in place of a ``to_prover9`` method.

    ``Class.to_prover9`` is a function of the node. ``node.to_prover9`` is the method that writes the
    prepared tree (:func:`_prover9_prepared`) when no ``to_prover9`` is in progress in this context, and
    the ORIGINAL bound method when one is: a nested call costs no stack frame of its own, so a deep
    formula is written as deep as it was before. ``__wrapped__`` is the original function.
    """

    def __init__(self, function: Callable[..., str]) -> None:
        for attribute in ("__module__", "__name__", "__qualname__", "__doc__"):
            setattr(self, attribute, getattr(function, attribute))
        self.__wrapped__ = function
        self._function = function

        @functools.wraps(function)
        def outermost(node: Any) -> str:
            return function(node) if _PROVER9_PREPARED.get() else _prover9_write_outermost(node)

        self._outermost = outermost

    def __get__(self, node: Any, owner: Any = None) -> Any:
        write = self._function if _PROVER9_PREPARED.get() else self._outermost
        return write if node is None else types.MethodType(write, node)


_F = TypeVar("_F", bound=Callable[..., str])


def _prover9_outermost(function: _F) -> _F:
    """Mark the ``to_prover9`` of a node class whose text can hold a binder, or stand around one:
    the outermost call prepares the whole node once (:func:`_prover9_prepared`), the calls nested in
    it write their nodes as they are."""
    return cast(_F, _Prover9Entry(function))


# --------------------------------------------------------------------------- #
# TPTP name folding — the exact mirror of tptp_input.py's ``_cap()``.
#
# TPTP requires an unquoted identifier to start with a lower-case letter
# (``lower_word: [a-z][A-Za-z0-9_]*``), while this kit's own Atom-predicate
# convention requires an upper-case first letter (grammar token
# ``PREDICATE: /[A-Z][a-zA-Z0-9]*/``). On import, ``tptp_input.py``'s
# ``_cap()`` bridges that gap by capitalising ONLY the first character of a
# parsed predicate name (``hasBond`` → ``HasBond``) and leaving every other
# character untouched — never a whole-string case fold. Exporting therefore
# has to invert exactly that: fold only the first character back to
# lower-case, not `.lower()` the entire name. An earlier version of
# Atom/Function/Constant.to_tptp did the latter, which is wrong two ways:
#
#  1. **Not the true inverse of `_cap()`.** ``_cap()`` only ever touches
#     position 0, so re-exporting a mixed-case name via whole-string
#     `.lower()` does not reproduce the original: a chemistry predicate like
#     ``BDouble`` would round-trip as ``bdouble`` → (re-imported, `_cap()`
#     applied) → ``Bdouble`` — a DIFFERENT symbol, silently.
#  2. **Loses information `_cap()` never touched at all for Function/Constant
#     names.** Those are never case-folded on import (`_functor_name` only
#     strips quotes), so a mixed-case function/constant name such as
#     ``hasBond`` needs NO folding whatsoever — the first character is
#     already lower-case per this kit's own NAME-token convention — yet the
#     old whole-string `.lower()` mangled it to ``hasbond`` anyway.
#
# Folding only the first character does NOT by itself make the export
# injective: ``Foo`` and ``foo`` still both fold to ``foo``. A collision is a
# property of the whole SET of symbols a text contains, never of one node, so
# it is caught where a set of symbols is known:
#
#  * for ONE formula, by the OUTERMOST ``to_tptp()`` call — every node class's
#    ``to_tptp`` is guarded (``Node.__init_subclass__``, see
#    :mod:`unicode_logic_kit.fol._tptp_symbols`), the guard records each name the
#    render actually writes and, when the outermost call returns, refuses with
#    ``NotImplementedError`` if two DISTINCT names of one kind (predicates; or
#    functions and constants together) were written as one word. It reads what
#    is rendered, not what is in the source tree, so a name a reduction
#    introduces (the sort guard predicate of a ``SortedQuantifier``) is seen;
#  * for a PROBLEM made of several formulas, by the checked writers —
#    :func:`unicode_logic_kit.atp._tptp_problem.generate_tptp_problem` (the
#    external-prover backends), the TF0/TFA writers, and
#    :func:`unicode_logic_kit.atp.tptp_ncl.to_tptp_ncl` (the NXF modal export) —
#    which check every premise and the conclusion TOGETHER. A caller that
#    joins ``to_tptp()`` strings itself is outside every check: ``gaseous`` in
#    one premise and ``Gaseous`` in another reach the prover as one symbol, and
#    no per-formula check can see it.
#
# Both use the SAME check (``_tptp_symbols.check_symbols``), reading the same
# per-node hook (``Node._tptp_symbol``), so they cannot disagree about what a
# node writes.
#
# What is refused and what is renamed differ, deliberately, for this release.
# Two LEGAL names of one kind that fold together (``Foo``/``foo``) are refused
# by name, by both the guard and the writers: the refusal predates the writers'
# name map, and stays so that no existing caller silently receives a symbol
# renamed behind its back. A name TPTP cannot spell, and a predicate that
# shares its word with a function/constant (the class ``Agent`` and the role
# function ``agent``), are renamed by the WRITERS and recorded in the returned
# ``TptpNameMap``. The guard does not refuse the cross-kind case: the text of
# one formula is unambiguous by position and this kit's reader reads it back,
# and only a writer has a map to hand back. A name TPTP cannot spell is another
# matter for ONE formula: the guard cannot rename it and will not write it, so
# it refuses it by name (an illegal word is not a rendering).
# --------------------------------------------------------------------------- #

def tptp_fold_first_letter(name: str) -> str:
    """Fold ``name``'s first character to lower-case for TPTP export; leave the rest untouched.

    The exact mirror of :func:`tptp_input._cap`, which capitalises only the
    first character of a parsed predicate name on import — see the module
    comment above this function for why a whole-string ``.lower()`` is wrong.
    Used by :meth:`Atom.to_tptp`, :meth:`Function.to_tptp`, and
    :meth:`Constant.to_tptp` for their predicate/function/constant name.
    """
    return (name[:1].lower() + name[1:]) if name else name


# The resolvers behind ``Node._tptp_symbol``: kit name -> (namespace, word, kind),
# exactly the word the matching ``to_tptp`` writes for it; ``None`` for a token
# that is not an identifier. Predicates are one namespace; functions and
# constants share the other.

def _predicate_symbol(name: str):
    # Equality and the comparisons are written with a token of their own
    # (``=``, ``!=``, ``$less`` ...). Such a token is not a name, but a user's
    # predicate named ``$less`` would be written as the same word.
    if name in Atom.INFIX_PREDS_TPTP:
        return ("predicate", Atom.INFIX_PREDS_TPTP[name], "reserved predicate")
    if name in Atom.PREFIX_PREDS_TPTP:
        return ("predicate", Atom.PREFIX_PREDS_TPTP[name], "reserved predicate")
    return ("predicate", tptp_fold_first_letter(name), "predicate")


def _function_symbol(name: str):
    if name in Function.TPTP_ARITH_OPS:
        return ("term", Function.TPTP_ARITH_OPS[name], "reserved function")
    return ("term", tptp_fold_first_letter(name), "function")


def _constant_symbol(name: str):
    return ("term", tptp_fold_first_letter(constant_name_to_ascii(name)), "constant/function")


def _measure_symbol(name: str):
    return ("term", name, "function")


def _variable_symbol(name: str):
    return ("variable", name.upper(), "variable")


def _numeral_symbol(value):
    # The word is the text the number is written as, which is also what a number
    # is called in a refusal. A value has one spelling (``Number(1.0)`` is
    # ``Number(1)``), so the value alone keys the entry of the render log.
    text = _number_text(value)
    return ("term", text, "numeral", text)


@dataclass(frozen=True)
class Constant(Node):
    """A ground constant, produced by a bare NAME, a ``c_``-prefixed CONSTANT, or a
    non-ASCII (Greek, e.g. ``θ``) CONSTANT token.

    The name may contain non-ASCII letters; the Kripke evaluator and Z3 use them
    directly, while the ASCII-only Prover9 / TPTP exporters transliterate them via
    :func:`constant_name_to_ascii` (``θ`` → ``theta``)."""

    name: str

    def to_dict(self):
        """Serialise to dict with type tag and constant name."""
        return {"_type": "Constant", "name": self.name}

    @staticmethod
    def from_dict(d):
        """Deserialise a Constant from a dict produced by to_dict."""
        return Constant(d["name"])

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 constant in the uninterpreted sort S (Z3 accepts the raw name)."""
        return (env or Z3Env()).get_symbol(self.name)

    def to_prover9(self) -> str:
        """Render the constant name, transliterating any non-ASCII to ASCII (Prover9 is ASCII-only).

        A name that begins with an upper-case letter or an underscore
        (:func:`_prover9_reads_as_variable`) is written in double quotes:
        ``Gaseous`` is written ``"Gaseous"``. Every Prover9 file this kit writes
        sets ``prolog_style_variables``, under which the bare word in term
        position is a VARIABLE when it begins with an upper-case letter, so
        ``P(Gaseous)`` would read as ``∀X P(X)`` and the text would denote a
        different formula (an underscore-initial name is a constant to Prover9
        itself, and is quoted all the same, because the Prolog convention reads
        it as a variable); a double-quoted symbol is
        never a variable and is a symbol of its own, distinct from the bare word
        of the same letters. The kit's own Prover9 reader reads it back as this
        constant.

        Raises:
            NotImplementedError: the name would be read as a variable and cannot
                be quoted, because it holds a character other than a letter, a
                digit or an underscore (LADR has no escape for a double quote
                inside quotes). A single node cannot rename (a rename must be the
                same in every formula of the problem and stay injective), so the
                refusal points at the problem writer, which does. A name that is
                no word at all (a space, a dot, a ``$``-word, empty) is refused the
                same way, whatever its first letter: written bare it would be read
                as several symbols or as one of Prover9's own.
        """
        text = constant_name_to_ascii(self.name)
        quoted = _prover9_arity_zero_symbol(text)
        if quoted is not None:
            return quoted
        if _prover9_reads_as_variable(text):
            raise NotImplementedError(
                f"to_prover9: constant {self.name!r} cannot be written for Prover9 on its "
                f"own: it would be read as a variable, and it cannot be put in double "
                f"quotes (which Prover9 never reads as a variable) because it holds a "
                f"character other than a letter, a digit or an underscore. Every "
                f"Prover9 file this kit writes sets prolog_style_variables, "
                f"under which a term-position symbol that begins with an upper-case "
                f"letter or an underscore is a VARIABLE: the text {text!r} would read "
                f"as a variable, and the formula around it would say something else "
                f"('P({text})' reads as 'for all X, P(X)'). Build the problem with "
                f"unicode_logic_kit.atp.prover9_entailment.generate_prover9_input_with_mapping "
                f"(check_logical_entailment and the Prover9 backend use it), which renames "
                f"such a constant to a lower-case token and returns the mapping, or name "
                f"the constant with a lower-case first letter.")
        raise _prover9_name_refusal("the constant", self.name, text)

    def to_tptp(self) -> str:
        """Render constant in TPTP syntax (ASCII, lowercase-initial): transliterate, then fold the first letter.

        Only the first character is folded to lower-case (see
        :func:`tptp_fold_first_letter`) — everything from the second character
        on is emitted verbatim, so a mixed-case constant name (e.g. a
        chemistry identifier like ``hasBond``) survives export unmangled.
        """
        return tptp_fold_first_letter(constant_name_to_ascii(self.name))

    def _tptp_symbol(self):
        """The constant word :meth:`to_tptp` writes (shares the term namespace with functions)."""
        return (_constant_symbol, self.name)


def _number_text(value) -> str:
    """The text a :class:`Number` prints as in every textual syntax of the kit
    (unicode, LaTeX, TPTP, Prover9), and that the kit's own readers read back as
    the SAME value.

    The NUMBER terminal of every reader is ``-?[0-9]+(\\.[0-9]+)?``: digits, an
    optional fractional part, no exponent. Python's ``str(1e-07)`` is ``'1e-07'``,
    which the unicode reader reads as the subtraction ``1e - 07`` and
    ``str(1.5e-05)`` is not text it can read at all. So a float whose ``repr`` is
    in exponent form is written in plain positional notation instead, from the
    digits of that same ``repr`` (the shortest string that round-trips) with
    decimal arithmetic, never a rounding format: ``float(text) == value`` exactly.
    A float always keeps a ``.`` so it reads back as a float, not an int
    (``1e16`` is ``10000000000000000.0``). An int, and every float whose ``repr``
    is already positional (``2.5``, ``12345.678``, ``0.0001``), prints exactly as
    before. A :class:`Number` never holds a float with a whole value (it stores the
    integer it equals, so ``Number(1e16)`` prints ``10000000000000000``); the point
    of such a raw float is kept only for a caller that hands a bare float to this
    function.

    Raises:
        ValueError: ``value`` is ``inf``, ``-inf`` or ``nan``. No syntax of the
            kit has a literal for it, and the word ``inf`` would read back as a
            CONSTANT of that name, a different formula.
    """
    if isinstance(value, float):
        if value != value or value in (float("inf"), float("-inf")):
            raise ValueError(
                f"Number({value!r}) has no literal: a non-finite float cannot be "
                f"written in the unicode, LaTeX, TPTP or Prover9 syntax, and the "
                f"word {str(value)!r} would read back as a constant of that name, "
                f"not as a number. Use a finite value (or a constant such as "
                f"'infinity' for a symbolic bound).")
        text = repr(float(value))
        if "e" in text or "E" in text:
            text = format(Decimal(text), "f")
            if "." not in text:
                text += ".0"
        return text
    return str(value)


#: The most significant digits a decimal text may have and still be read as the float it spells.
_DECIMAL_DIGITS_READ_EXACTLY = 15

#: The smallest positive normal double (``sys.float_info.min``): below it the doubles carry fewer
#: than 53 significant bits.
_SMALLEST_NORMAL_DOUBLE = 2.2250738585072014e-308


def _numeral_from_text(text: str) -> Union[int, float]:
    """The value of a decimal numeral as it is written, ``-?[0-9]+(\\.[0-9]+)?``: read exactly or refused.

    This is the ONE reading every text reader of the kit gives a NUMBER token, the inverse of
    :func:`_number_text`. A text without a point is the ``int`` of its digits, and so is a text
    with a point whose fractional digits are all zero, whatever its size
    (``100000000000000000000000.0`` is 10**23, where ``float`` would give the nearest double,
    ``99999999999999991611392``). Any other decimal is the ``float`` it spells when it has at most
    15 significant digits, counted after the sign, the leading zeros and the trailing zeros of the
    fraction are dropped (``0.1`` and ``0.10`` are one numeral, ``3.14159265358979`` is read), and
    is refused when it has more (``3.141592653589793``).

    Fifteen is the bound because two different decimals of at most 15 significant digits differ by
    at least 1e-15 of the larger one, while two numbers that are one double differ by at most
    2**-52 (about 2.2e-16) of it, so no two such decimals are one float. With 16 digits the gap can
    be 1e-16 of the number, below the spacing of the doubles, and two decimals can be one float
    (``8.000000000000001`` and ``8.000000000000002``, ``0.30000000000000004`` and
    ``0.30000000000000005``).

    Raises:
        ValueError: the decimal has more than 15 significant digits (two different decimals of that
            length can be one float, and a numeral is identified by its value, so reading it as a
            float could make two numerals one), or is nearer to zero than the smallest normal
            double (2.2250738585072014e-308), where a double holds fewer than 15 digits and a
            different decimal can be the same double, or zero. The message names the numeral and
            says why; a numeral is never read as another one.
    """
    whole, point, fraction = text.partition(".")
    if not point:
        return int(text)
    if not fraction.strip("0"):
        return int(whole)
    digits = len((whole.lstrip("+-") + fraction.rstrip("0")).lstrip("0"))
    if digits > _DECIMAL_DIGITS_READ_EXACTLY:
        raise ValueError(
            f"the numeral {text} has {digits} significant digits, more than the "
            f"{_DECIMAL_DIGITS_READ_EXACTLY} that a floating-point number tells apart: two different "
            f"decimals of that length can be one float (0.30000000000000004 and 0.30000000000000005 "
            f"are), and a numeral is identified by its value, so reading it as a float could make "
            f"two numerals one. Write it with at most {_DECIMAL_DIGITS_READ_EXACTLY} significant "
            f"digits, or as an integer")
    value = float(text)
    if abs(value) < _SMALLEST_NORMAL_DOUBLE:
        raise ValueError(
            f"the numeral {text} is so close to zero that a floating-point number cannot hold "
            f"{_DECIMAL_DIGITS_READ_EXACTLY} digits of it (the nearest float is {value!r}), and "
            f"reading it as that number could make two different numerals one. Write it as 0, or "
            f"with a larger magnitude")
    return value


class NumeralTextError(ParsingError):
    """A numeral the unicode reader cannot read as the number it was written as.

    A :class:`~unicode_logic_kit.fol.naming.ParsingError`, so the CLI, ``api.parse_any`` and every
    caller that catches the parser's error type report it as the one-line SYNTAX_ERROR it is. It
    is constructed directly from the message of :func:`_numeral_from_text`, not from a Lark
    exception, so it sets its own message.
    """

    def __init__(self, message: str):
        self.args = (f"SYNTAX_ERROR: {message}",)

    def __str__(self):
        return self.args[0]


@dataclass(frozen=True)
class Number(Node):
    """A numeral, produced by the NUMBER terminal of the grammar: a constant identified by its VALUE.

    On every route that was not asked for arithmetic by name a numeral is an ordinary constant
    and nothing else is known about it: two numerals of different value may denote the same
    element (``1 ≠ 2`` is not valid), ``+ - * /`` are uninterpreted function symbols and
    ``< > ≤ ≥`` uninterpreted predicates. The arithmetic reading is asked for by name (the
    ``*_arith`` functions and ``sort="int"`` / ``sort="real"``); there ``Number(3)`` is the
    integer 3, or the real 3.0 under ``sort="real"``.

    There is ONE constant per value and ONE spelling per value. A float whose value is a whole
    number is stored as the ``int`` it equals: ``Number(1.0)`` IS ``Number(1)``, with the same
    ``value``, the same ``repr``, the same ``to_dict`` and the same printed text (``1``) in every
    syntax, and ``Number(-0.0)`` is ``Number(0)``. A value that is no whole number keeps its type
    (``Number(2.5)`` is a float). A float too large to have a fractional part is the integer it
    exactly is (the double nearest ``1e23`` is ``99999999999999991611392``).

    The readers read a decimal text exactly or refuse it. One whose fractional digits are all zero
    is the integer it spells (``100000000000000000000000.0`` is ``10**23``, not that double), any
    other is the float it spells when it has at most 15 significant digits (``0.1`` and ``0.10``
    are one numeral), and one with more is refused by name, because two different decimals of 16
    digits or more can be one float (``0.30000000000000004`` and ``0.30000000000000005`` are) and
    a numeral is identified by its value.

    Numerals of equal value are equal nodes and print alike, so a route that keys an atom by its
    printed text reads ``P(1)`` and ``P(1.0)`` as the one atom they are. A ``bool`` is no number:
    it is kept as it is, not read as ``1`` or ``0``, and the routes that need an integer refuse
    it by name.

    Fields:

    * ``value`` -- the number: an ``int``, or a ``float`` that is not a whole number (a
      non-finite float is stored as it is; no syntax of the kit has a literal for it).
    """

    value: Union[int, float]

    def __post_init__(self):
        """Store a float with a whole value as the ``int`` it equals: one numeral, one spelling."""
        value = self.value
        if isinstance(value, float) and value.is_integer():
            object.__setattr__(self, "value", int(value))

    def to_dict(self):
        """Serialise to dict with type tag and numeric value (an integral value is an ``int``)."""
        return {"_type": "Number", "value": self.value}

    @staticmethod
    def from_dict(d):
        """Deserialise a Number from a dict produced by to_dict."""
        return Number(d["value"])

    def to_z3(self, env: Z3Env = None):
        """Encode the number as a named constant in the uninterpreted sort S.

        The symbol is named by the VALUE of the number (:func:`numeral_key`), so
        ``Number(1)`` and ``Number(1.0)`` are one constant, and a constant of that very
        name would be the same symbol; the environment refuses the pair (see
        :class:`Z3Env`) with a ``NotImplementedError``. Nothing else is known about a
        numeral: ``1`` and ``2`` may denote the same element.
        """
        return (env or Z3Env()).get_symbol(numeral_key(self.value), numeral=True)

    def to_prover9(self) -> str:
        """Render the numeral as ONE Prover9 constant: its value in double quotes.

        A numeral is a constant identified by its VALUE, so ``Number(1)`` and
        ``Number(1.0)`` -- equal nodes -- are one symbol, ``"1"``; ``2.5`` is
        ``"2.5"`` and ``-1`` is ``"-1"``, the positional text of the number (see
        :func:`~unicode_logic_kit.fol._numeral_symbols.numeral_name`: an integral
        float is spelled as the integer, nothing is written in exponent form).
        The kit's Prover9 reader reads that quoted text back as the
        :class:`Number`.

        Every numeral is quoted, also a non-negative integer, for three reasons
        measured on Prover9 and Mace4 2026-8A. Bare, ``2.5`` ends the statement
        (Prover9 refuses the file) and ``-1`` is the function ``-`` applied to the
        constant ``1``. And Mace4 reads a bare integer as a domain element of its own,
        all of them pairwise distinct (``1 != 2`` has no countermodel at any size it
        searched, and the smallest model of ``P(1) & P(2)`` has three elements), whereas
        the kit's numerals are ordinary constants that may denote one thing (``⊢ 1 ≠ 2``
        is not valid); a quoted symbol is a plain constant to both tools. Prover9 has no arithmetic: ``+ - * /`` and
        ``< > ≤ ≥`` are uninterpreted symbols, as they are for the Z3 route.
        """
        from ._numeral_symbols import numeral_name
        return '"' + numeral_name(self.value) + '"'

    def to_tptp(self) -> str:
        """Render number in TPTP syntax as an integer or rational literal, a float in positional notation (see :func:`_number_text`).

        This is the ARITHMETIC spelling: a bare TPTP number is a literal of the prover's own
        arithmetic (Vampire and E type ``1`` as ``$int``, so ``p(1)`` is a type error for a
        predicate over individuals, and ``1 != 2`` is a theorem). On every route that was not
        asked for arithmetic the kit reads a numeral as a CONSTANT identified by its value, and a
        PROBLEM for a prover is written by the checked writers
        (:func:`~unicode_logic_kit.atp._tptp_problem.generate_tptp_problem_with_mapping`,
        :func:`~unicode_logic_kit.atp.tptp_tff.generate_tff_problem_with_mapping`), which write the
        numeral as an ordinary constant of a word of their own and record it in the name map.
        Use this method for the text of ONE formula, never to assemble a problem.
        """
        return _number_text(self.value)

    def _tptp_symbol(self):
        """The numeral :meth:`to_tptp` writes, which is also the word of a constant spelled like it."""
        return (_numeral_symbol, self.value)


@dataclass(frozen=True)
class Function(Node):
    """A function application node, covering both named functions and arithmetic operators."""

    name: str
    args: Tuple[Node, ...]

    def __post_init__(self):
        """Coerce args to a tuple so this frozen node is hashable."""
        if not isinstance(self.args, tuple):
            object.__setattr__(self, "args", tuple(self.args))

    INFIX_OPS = {"+", "-", "*", "/"}

    def to_dict(self):
        """Serialise to dict with type tag, function name, and recursively serialised arguments."""
        return {
            "_type": "Function",
            "name": self.name,
            "args": [a.to_dict() for a in self.args]
        }

    @staticmethod
    def from_dict(d):
        """Deserialise a Function from a dict produced by to_dict."""
        return Function(d["name"], [Node.from_dict(a) for a in d["args"]])

    def to_z3(self, env: Z3Env = None):
        """Translate to an uninterpreted Z3 function application in sort S."""
        env = env or Z3Env()
        z3_args = [a.to_z3(env) for a in self.args]
        func = env.get_func(self.name, len(self.args))
        return func(*z3_args)

    def to_prover9(self) -> str:
        """Render in Prover9 syntax, using infix notation for ``+``, ``*`` and ``/``.

        Prover9 has no infix minus: ``(a - b)`` is a syntax error there (measured on
        2026-8A), so a binary ``-`` is written in functional notation, ``-(a, b)``,
        the same symbol that ``-(a)`` is at one argument. None of these symbols is
        interpreted by Prover9, as none is by the Z3 route: they are uninterpreted
        functions. A function with no arguments is a constant (see
        :meth:`Constant.to_prover9`).

        Raises:
            NotImplementedError: the name is no word Prover9 reads as one symbol (a
                space, a dot, a non-ASCII letter, a ``$``-word, an arithmetic
                symbol at a number of arguments it has no notation for); the problem
                writer renames such a name.
        """
        if self.name in self.INFIX_OPS and len(self.args) == 2:
            left = self.args[0].to_prover9()
            right = self.args[1].to_prover9()
            if self.name == "-":
                return f"-({left}, {right})"
            return f"({left} {self.name} {right})"
        if self.name == "-" and len(self.args) == 1:
            return f"-({self.args[0].to_prover9()})"
        if not self.args:
            return Constant(self.name).to_prover9()

        name = _prover9_word(self.name, "the function", len(self.args))
        args_str = ", ".join(a.to_prover9() for a in self.args)
        return f"{name}({args_str})"

    TPTP_ARITH_OPS = {
        "+": "$sum",
        "-": "$difference",
        "*": "$product",
        "/": "$quotient",
    }

    def to_tptp(self) -> str:
        """Render function application in TPTP syntax.

        Arithmetic operators (``+``, ``-``, ``*``, ``/``) are mapped to their
        TPTP dollar-word equivalents (``$sum``, ``$difference``, ``$product``,
        ``$quotient``) and emitted in
        prefix notation. All other functions are emitted as identifiers with
        a parenthesised argument list, with only the first character folded
        to lower-case (see :func:`tptp_fold_first_letter`) — a mixed-case
        function name is otherwise preserved verbatim.

        The dollar-words are the ARITHMETIC spelling: a prover reads ``$sum(1,1) = 2`` as a
        theorem of its own arithmetic. On every route that was not asked for arithmetic the kit
        reads ``+ - * /`` as uninterpreted function symbols, and a PROBLEM for a prover is
        written by the checked writers
        (:func:`~unicode_logic_kit.atp._tptp_problem.generate_tptp_problem_with_mapping`,
        :func:`~unicode_logic_kit.atp.tptp_tff.generate_tff_problem_with_mapping`), which write
        the operator as an ordinary function of a word of their own and record it in the name
        map; the typed arithmetic writer
        (:func:`~unicode_logic_kit.atp._tff_problem.generate_tff_arith_problem`) keeps the
        dollar-words, typed ``$int`` or ``$real``. Use this method for the text of ONE formula,
        never to assemble a problem.

        A function with no arguments is the constant of its name, and is written as that
        constant (:meth:`Constant.to_tptp`): TPTP has no empty argument list, ``f()`` is no
        term, and a prover stops at it with a parse error. The refusals of the constant apply to
        it, so an arithmetic symbol with no argument (``+``) is refused by name rather than
        written as ``$sum()``.
        """
        if not self.args:
            return Constant(self.name).to_tptp()
        args_str = ",".join(a.to_tptp() for a in self.args)
        tptp_name = self.TPTP_ARITH_OPS.get(self.name, tptp_fold_first_letter(self.name))
        return f"{tptp_name}({args_str})"

    def _tptp_symbol(self):
        """The word :meth:`to_tptp` writes: the function word, or for a function with no arguments the word of the constant of its name (an arithmetic operator is a fixed ``$``-word)."""
        if not self.args:
            return (_constant_symbol, self.name)
        return (_function_symbol, self.name)


# =========================
# Formula Nodes
# =========================

@dataclass(frozen=True)
class Atom(Node):
    """An atomic formula: either a named predicate application or an infix comparison."""

    predicate: str
    args: Tuple[Node, ...]

    def __post_init__(self):
        """Coerce args to a tuple so this frozen node is hashable."""
        if not isinstance(self.args, tuple):
            object.__setattr__(self, "args", tuple(self.args))

    INFIX_PREDS_P9 = {
        "=": "=", "<": "<", ">": ">",
        "≤": "<=", "≥": ">=", "≠": "!=",
    }

    def to_dict(self):
        """Serialise to dict with type tag, predicate name, and recursively serialised arguments."""
        return {
            "_type": "Atom",
            "predicate": self.predicate,
            "args": [a.to_dict() for a in self.args]
        }

    @staticmethod
    def from_dict(d):
        """Deserialise an Atom from a dict produced by to_dict."""
        return Atom(d["predicate"], [Node.from_dict(a) for a in d["args"]])

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 boolean expression.

        Equality and disequality map to native Z3 operators; all other
        predicates become uninterpreted Z3 functions returning Bool. The nullary
        atoms ``$true`` and ``$false`` (TPTP's defined propositions, which this
        kit's TPTP reader produces) are the constants true and false, so z3 and a
        TPTP prover answer the question the TPTP text asks; the nullary atoms named
        ``⊤`` and ``⊥`` are the same two constants.
        """
        env = env or Z3Env()
        if _is_tptp_boolean_atom(self):
            return z3.BoolVal(_truth_constant_word(self) == "$true")
        z3_args = [a.to_z3(env) for a in self.args]

        if self.predicate == "=" and len(self.args) == 2:
            return z3_args[0] == z3_args[1]
        if self.predicate == "≠" and len(self.args) == 2:
            return z3_args[0] != z3_args[1]

        pred = env.get_pred(self.predicate, len(self.args))
        return pred(*z3_args)

    def to_prover9(self) -> str:
        """Render in Prover9 syntax, using infix notation for comparison predicates.

        A nullary predicate renders as a propositional atom without an argument
        list; Prover9 rejects an empty one (``P()``). The nullary atoms ``$true``
        and ``$false`` (TPTP's defined propositions, see :meth:`to_z3`) are
        Prover9's constants ``$T`` and ``$F``.

        A predicate whose name is no word (a space, a dot, a non-ASCII letter, a
        ``$``-word, empty) is refused by name, at every arity: written bare it would
        be read as several symbols or as one of Prover9's own, and it cannot be
        quoted. A comparison symbol at a number of arguments other than two is
        refused the same way.

        A nullary predicate that begins with an upper-case letter or an underscore
        — ``Rain``, the usual spelling of a proposition in this kit — is written in
        double quotes, ``"Rain"``. Every Prover9 file this kit writes sets
        ``prolog_style_variables``, under which an arity-0 symbol that begins with
        an upper-case letter is a VARIABLE, an atom with no arguments included
        (measured on Prover9 2026-8A: the bare ``Rain`` is refused as "cannot be
        used as atomic formulas, because they are variables"). A double-quoted
        symbol is never a variable and is a symbol of its own, distinct from the
        bare word of the same letters; the kit's own Prover9 reader reads it back
        as this atom. A lower-case nullary predicate is written bare. The same
        word used both as a proposition and as a constant, or as a predicate of
        two arities, is one symbol to Prover9,
        which refuses the file; this method has no view of the other formulas and
        cannot see that. The problem writer (:func:`unicode_logic_kit.atp
        .prover9_entailment.generate_prover9_input_with_mapping`) renames such
        symbols to lower-case tokens, one per role, and records the renaming; text
        for Prover9 is built with the writer, not by joining ``to_prover9()``
        strings.
        """
        if self.predicate in self.INFIX_PREDS_P9 and len(self.args) == 2:
            left = self.args[0].to_prover9()
            right = self.args[1].to_prover9()
            op = self.INFIX_PREDS_P9[self.predicate]
            return f"({left} {op} {right})"

        if _is_tptp_boolean_atom(self):
            return "$T" if _truth_constant_word(self) == "$true" else "$F"

        if not self.args:
            quoted = _prover9_arity_zero_symbol(self.predicate)
            if quoted is None:
                raise _prover9_name_refusal("the proposition", self.predicate)
            return quoted

        name = _prover9_word(self.predicate, "the predicate", len(self.args))
        args_str = ", ".join(a.to_prover9() for a in self.args)
        return f"{name}({args_str})"

    # The only genuine infix predicates in TPTP are equality and disequality.
    INFIX_PREDS_TPTP = {
        "=": "=",
        "≠": "!=",
    }

    # Arithmetic comparisons are TPTP dollar-word predicates, applied in
    # prefix/functor form ($less(a, b)) — they are NOT infix operators.
    PREFIX_PREDS_TPTP = {
        "<": "$less",
        ">": "$greater",
        "≤": "$lesseq",
        "≥": "$greatereq",
    }

    def to_tptp(self) -> str:
        """Render an atom in TPTP syntax.

        Equality (=) and disequality (!=) are emitted infix — the only genuine
        infix predicates in TPTP. The arithmetic comparisons (<, >, ≤, ≥) are
        TPTP dollar-word predicates and are emitted in prefix/functor form
        ($less(a, b), $greater(a, b), $lesseq(a, b), $greatereq(a, b)). All
        other predicates are emitted as identifiers with a parenthesised
        argument list, with only the first character folded to lower-case
        (see :func:`tptp_fold_first_letter`) — the exact mirror of
        ``tptp_input.py``'s ``_cap()``, which capitalises only the first
        character of a parsed predicate name on import. A nullary predicate
        becomes a bare propositional atom.

        The four comparisons are the ARITHMETIC spelling: a prover proves
        ``$less(1,2)`` from its own arithmetic. On every route that was not asked for
        arithmetic the kit reads ``< > ≤ ≥`` as uninterpreted binary predicates, and a
        PROBLEM for a prover is written by the checked writers
        (:func:`~unicode_logic_kit.atp._tptp_problem.generate_tptp_problem_with_mapping`,
        :func:`~unicode_logic_kit.atp.tptp_tff.generate_tff_problem_with_mapping`), which write a
        comparison as an ordinary predicate of a word of its own and record it in the name
        map; the typed arithmetic writer
        (:func:`~unicode_logic_kit.atp._tff_problem.generate_tff_arith_problem`) keeps the
        dollar-words. Use this method for the text of ONE formula, never to assemble a
        problem.

        This first-letter fold is NOT injective on its own — ``Foo`` and
        ``foo`` both render as ``foo`` — so two distinct predicates that
        differ only in their first letter's case collide. Inside ONE formula
        the outermost ``to_tptp()`` call refuses that (see
        :meth:`Node.to_tptp`); across several formulas only the checked
        problem writers can, since a single formula has no visibility into its
        siblings elsewhere in the problem.

        The two truth constants are TPTP's own words: the nullary atoms ``$true``
        and ``⊤`` are written ``$true``, ``$false`` and ``⊥`` are written ``$false``.
        """
        truth_word = _truth_constant_word(self)
        if truth_word is not None:
            return truth_word

        if self.predicate in self.INFIX_PREDS_TPTP and len(self.args) == 2:
            left = self.args[0].to_tptp()
            right = self.args[1].to_tptp()
            op = self.INFIX_PREDS_TPTP[self.predicate]
            return f"({left} {op} {right})"

        if self.predicate in self.PREFIX_PREDS_TPTP and len(self.args) == 2:
            left = self.args[0].to_tptp()
            right = self.args[1].to_tptp()
            op = self.PREFIX_PREDS_TPTP[self.predicate]
            return f"{op}({left},{right})"

        if not self.args:
            return tptp_fold_first_letter(self.predicate)

        args_str = ",".join(a.to_tptp() for a in self.args)
        return f"{tptp_fold_first_letter(self.predicate)}({args_str})"

    def _tptp_symbol(self):
        """The predicate word :meth:`to_tptp` writes (none for equality and the arithmetic comparisons: fixed tokens).

        None for the nullary atoms ``$true`` / ``$false`` either: they are TPTP's own
        propositions, written verbatim, and no symbol of the user's."""
        if _is_tptp_boolean_atom(self):
            return None
        return (_predicate_symbol, self.predicate)


@dataclass(frozen=True)
class Not(Node):
    """Logical negation of a formula."""

    formula: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Not", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Not from a dict produced by to_dict."""
        return Not(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Not expression."""
        return z3.Not(self.formula.to_z3(env or Z3Env()))

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render negation in Prover9 syntax using the dash operator."""
        return f"-({self.formula.to_prover9()})"

    def to_tptp(self) -> str:
        """Render negation in TPTP syntax using the tilde operator."""
        return f"~({self.formula.to_tptp()})"


@dataclass(frozen=True)
class And(Node):
    """Conjunction of two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "And", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an And from a dict produced by to_dict."""
        return And(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 And expression."""
        env = env or Z3Env()
        return z3.And(self.left.to_z3(env), self.right.to_z3(env))

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render conjunction in Prover9 syntax using the ampersand operator."""
        return f"({self.left.to_prover9()} & {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render conjunction in TPTP syntax using the ampersand operator."""
        return f"({self.left.to_tptp()} & {self.right.to_tptp()})"


@dataclass(frozen=True)
class Or(Node):
    """Disjunction of two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Or", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Or from a dict produced by to_dict."""
        return Or(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Or expression."""
        env = env or Z3Env()
        return z3.Or(self.left.to_z3(env), self.right.to_z3(env))

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render disjunction in Prover9 syntax using the pipe operator."""
        return f"({self.left.to_prover9()} | {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render disjunction in TPTP syntax using the pipe operator."""
        return f"({self.left.to_tptp()} | {self.right.to_tptp()})"


@dataclass(frozen=True)
class Xor(Node):
    """Exclusive disjunction of two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Xor", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Xor from a dict produced by to_dict."""
        return Xor(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Xor expression."""
        env = env or Z3Env()
        return z3.Xor(self.left.to_z3(env), self.right.to_z3(env))

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render exclusive or in Prover9 syntax by expanding to (l | r) & -(l & r)."""
        l = self.left.to_prover9()
        r = self.right.to_prover9()
        return f"(({l} | {r}) & -(({l}) & ({r})))"

    def to_tptp(self) -> str:
        """Render exclusive or in TPTP syntax using the non-equivalence operator (<~>).

        In TPTP ``~|`` is NOR, not XOR; ``<~>`` (non-equivalence) is the operator
        truth-functionally equal to exclusive or.
        """
        return f"({self.left.to_tptp()} <~> {self.right.to_tptp()})"


@dataclass(frozen=True)
class Implies(Node):
    """Material implication from left to right."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Implies", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Implies from a dict produced by to_dict."""
        return Implies(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Implies expression."""
        env = env or Z3Env()
        return z3.Implies(self.left.to_z3(env), self.right.to_z3(env))

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render implication in Prover9 syntax using the -> operator."""
        return f"({self.left.to_prover9()} -> {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render implication in TPTP syntax using the => operator."""
        return f"({self.left.to_tptp()} => {self.right.to_tptp()})"


@dataclass(frozen=True)
class Iff(Node):
    """Biconditional (if and only if) between two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Iff", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Iff from a dict produced by to_dict."""
        return Iff(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to Z3 equality of the two boolean subexpressions."""
        env = env or Z3Env()
        return self.left.to_z3(env) == self.right.to_z3(env)

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render biconditional in Prover9 syntax using the <-> operator."""
        return f"({self.left.to_prover9()} <-> {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render biconditional in TPTP syntax using the <=> operator."""
        return f"({self.left.to_tptp()} <=> {self.right.to_tptp()})"


@dataclass(frozen=True)
class Quantifier(Node):
    """A universally or existentially quantified formula over a single variable."""

    type: str
    variable: Variable
    formula: Node

    def to_dict(self):
        """Serialise to dict with type tag, quantifier type, variable, and recursively serialised body."""
        return {
            "_type": "Quantifier",
            "type": self.type,
            "variable": self.variable.to_dict(),
            "formula": self.formula.to_dict()
        }

    @staticmethod
    def from_dict(d):
        """Deserialise a Quantifier from a dict produced by to_dict."""
        return Quantifier(d["type"], Node.from_dict(d["variable"]), Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 ForAll or Exists expression over the bound variable."""
        env = env or Z3Env()
        z3_var = self.variable.to_z3(env)
        body = self.formula.to_z3(env)

        if self.type in ("forall", "∀"):
            return z3.ForAll([z3_var], body)
        elif self.type in ("exists", "∃"):
            return z3.Exists([z3_var], body)
        raise ValueError(f"Unknown quantifier: {self.type}")

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render the quantified formula in Prover9 syntax using all/exists keywords.

        A binder that sits inside the scope of a binder of its own name is written under a fresh
        variable, so that Prover9 has nothing to rename (see :meth:`Node.to_prover9`).
        """
        var = self.variable.to_prover9()
        body = self.formula.to_prover9()

        if self.type in ("forall", "∀"):
            return f"(all {var} {body})"
        elif self.type in ("exists", "∃"):
            return f"(exists {var} {body})"
        raise ValueError(f"Unknown quantifier: {self.type}")

    def to_tptp(self) -> str:
        """Render a quantified formula in TPTP syntax.

        Universal quantification uses ! and existential uses ?,
        with the bound variable listed in brackets: ![X]: body or ?[X]: body.
        """
        var = self.variable.to_tptp()
        body = self.formula.to_tptp()

        if self.type in ("forall", "∀"):
            return f"(![{var}]: {body})"
        elif self.type in ("exists", "∃"):
            return f"(?[{var}]: {body})"
        raise ValueError(f"Unknown quantifier: {self.type}")


# =========================
# Counting quantifier, measure / cardinality terms, concessive connective
# =========================
#
# Classical, non-modal extensions used by natural-language → logic front-ends
# (e.g. CCG pipelines) to translate cardinal determiners, degree comparatives,
# counting comparisons, and concessive coordination:
#
#   * Count       — a cardinality quantifier ∃≥n / ∃≤n / ∃=n carrying its bound n
#                   SYMBOLICALLY (a Number, not expanded into single-letter
#                   variables), so an arbitrarily large n is represented exactly.
#                   It is first-order expressible; the exports lower it to the
#                   standard distinct-witnesses encoding via _expand().
#   * Measure     — a degree/measure term μ(entity, dimension) for bare quantity
#                   comparatives (μ(x, height) > μ(y, height)); an uninterpreted
#                   binary function on export.
#   * Cardinality — a set-cardinality term |{v : φ}| for counting comparisons
#                   (|{v : Votes(x, v)}| > |{v : Votes(y, v)}|). Set cardinality is
#                   a second-order notion, so it has NO first-order export.
#   * Contrast    — a concessive connective (whereas / although / but) that is
#                   truth-functionally ∧, but kept as a distinct node so the
#                   concession survives translation instead of flattening to ∧.
#
# Count and Cardinality BIND their variable, so the binder-aware passes in
# _msfl_nodes.py (free_variables / substitute / resolve_lambda_scope) special-case
# them alongside Quantifier, and the renderers special-case Count / Measure /
# Cardinality (binders/terms are not regular operators). Contrast IS a regular
# level2 operator and is driven entirely by the operator registry — it needs no
# renderer branch and no binder handling.

# op code -> the ∃-prefixed surface glyph (and its inverse, used by the parser).
_COUNT_OPS = {"ge": "∃≥", "le": "∃≤", "eq": "∃="}
_COUNT_TOKEN_TO_OP = {glyph: op for op, glyph in _COUNT_OPS.items()}

# Largest witness count Count._expand() will materialise. The distinct-witnesses
# encoding is O(n²) constraints under n nested quantifiers, so a large n produces a
# tree that is both huge and deeper than Python's recursion limit; the Count node
# itself keeps n symbolically and round-trips for ANY n, so only the to_z3 / to_prover9
# / to_tptp *expansion* is bounded.
_COUNT_EXPAND_MAX = 500
_COUNT_TOO_LARGE = (
    "Count.to_z3/to_prover9/to_tptp: n={n} is too large to expand to first-order "
    "(the distinct-witnesses encoding materialises O(n²) constraints under n nested "
    "quantifiers; the limit is n<={limit}). The Count node keeps n symbolically and "
    "round-trips via to_unicode_str / to_dict for any n — only this first-order "
    "lowering is bounded."
)


def _balanced_and(parts):
    """Fold a non-empty list of formulas into a *balanced* And tree (shallow depth).

    A left-associative fold would make an n-element conjunction n deep, so an
    O(n²)-conjunct counting expansion overflows Python's recursion limit on
    traversal; a balanced tree is only O(log n) deep.
    """
    while len(parts) > 1:
        merged = [And(parts[i], parts[i + 1]) for i in range(0, len(parts) - 1, 2)]
        if len(parts) % 2:
            merged.append(parts[-1])
        parts = merged
    return parts[0]


@dataclass(frozen=True)
class Count(Node):
    """A counting (cardinality) quantifier ∃≥n / ∃≤n / ∃=n over a single variable.

    ``op`` is ``"ge"`` / ``"le"`` / ``"eq"`` (at least / at most / exactly); ``n``
    is a :class:`Number` wrapping a non-negative integer bound — kept SYMBOLIC, not
    expanded into single-letter variables, so an arbitrarily large bound (e.g. 500)
    is represented exactly. ``variable`` is the bound counting variable and
    ``formula`` its matrix. Semantics: ``∃≥n x φ`` is true iff at least ``n``
    DISTINCT individuals satisfy ``φ`` (``∃≤n`` at most, ``∃=n`` exactly). The
    counting quantifier is first-order expressible; :meth:`to_z3` / :meth:`to_prover9`
    / :meth:`to_tptp` lower it to the standard distinct-witnesses encoding (see
    :meth:`_expand`).
    """

    op: str
    n: Number
    variable: Variable
    formula: Node

    def __post_init__(self):
        """Validate the op code and that n is a non-negative integer Number."""
        if self.op not in _COUNT_OPS:
            raise ValueError(
                f"Count: unknown op {self.op!r}; expected one of 'ge', 'le', 'eq'.")
        if not (isinstance(self.n, Number) and isinstance(self.n.value, int)
                and self.n.value >= 0):
            raise ValueError(
                "Count: n must be a Number wrapping a non-negative integer.")

    def _tree_parts(self):
        """Return the ∃≥n / ∃≤n / ∃=n label (with the bound variable) and the matrix."""
        return (f"{_COUNT_OPS[self.op]}{self.n.value} {self.variable.name}",
                [self.formula])

    def to_dict(self):
        """Serialise to dict with op, n, bound variable, and serialised matrix."""
        return {"_type": "Count", "op": self.op, "n": self.n.to_dict(),
                "variable": self.variable.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Count from a dict produced by to_dict."""
        return Count(d["op"], Node.from_dict(d["n"]),
                     Node.from_dict(d["variable"]), Node.from_dict(d["formula"]))

    def _expand(self, avoid_names=None) -> "Node":
        """Lower to plain FOL via the standard distinct-witnesses counting encoding.

        ``avoid_names`` is a set the caller owns: every name in it is avoided as a
        witness too (the problem writers pass every variable name of the whole
        problem), and every witness minted is added to it, so that a second
        expansion with the same set mints other names.

        ``∃≥m x φ`` becomes ``∃x0 … ∃x{m-1} (⋀ φ[x_i] ∧ ⋀_{i<j} x_i ≠ x_j)``;
        ``∃≤n`` is ``¬(∃≥n+1)``; ``∃=n`` is ``∃≥n ∧ ¬(∃≥n+1)``. The witnesses are
        named like the counting variable, one letter and digits (``x0``, ``x1``, …:
        the shape the VARIABLE terminal reads back, so the printed expansion parses),
        and they avoid EVERY name in the matrix, bound ones included, so the
        substitution below never has to rename an inner binder. The bound variable
        is substituted out capture-avoidingly, so the result is a closed,
        meaning-preserving classical formula.

        "Every name" means a name of EVERY kind that the matrix holds
        (:func:`~unicode_logic_kit.fol._identifiers.symbol_names`): the constants,
        and also the functions (the nullary one is a constant), the predicates and
        the sorts. A constant may be spelled like a variable — the grammar cannot
        write one, but a caller who builds nodes can, and so do the
        description-logic image (an individual named ``y0``) and the TPTP reader
        (``p(x0)``). ``Variable("y0")`` and ``Constant("y0")`` print the same and
        are the same symbol in a text with one namespace, so a witness named ``y0``
        would CAPTURE that constant: ``∃≥1 y1 r(y0, y1)`` used to expand to
        ``∃y0 r(y0, y0)``, which an irreflexive ``r`` contradicts — a consistent
        knowledge base came out inconsistent. A witness named like a predicate or
        a function is the same defect in SMT-LIB text, where a bound variable and
        the symbol it shadows are one identifier (``(exists ((x0 S)) (x0 x0))``).
        What the matrix does not hold is the caller's to pass: the other formulas
        of the problem, in ``avoid_names``.
        """
        from ._msfl_nodes import substitute  # lazy: avoid import cycle
        if self.n.value > _COUNT_EXPAND_MAX:
            raise NotImplementedError(
                _COUNT_TOO_LARGE.format(n=self.n.value, limit=_COUNT_EXPAND_MAX))
        var, phi = self.variable, self.formula
        avoid = set(_identifiers.symbol_names(phi)) | {var.name}
        if avoid_names is not None:
            avoid |= avoid_names

        def fresh(k):
            """Return k fresh Variables not clashing with the matrix or each other."""
            out = []
            for _ in range(k):
                name = _identifiers.fresh_variable_like(var.name, avoid)
                avoid.add(name)
                if avoid_names is not None:
                    avoid_names.add(name)
                out.append(Variable(name))
            return out

        def at_least(m):
            """Build the plain-FOL 'at least m distinct φ' formula."""
            if m <= 0:
                # '≥ 0' is vacuously true: ∃x (φ ∨ ¬φ), valid on a non-empty domain.
                w = fresh(1)[0]
                g = substitute(phi, var, w)
                return Quantifier("∃", w, Or(g, Not(g)))
            ws = fresh(m)
            conjuncts = [substitute(phi, var, w) for w in ws]
            conjuncts += [Atom("≠", [ws[i], ws[j]])
                          for i in range(m) for j in range(i + 1, m)]
            body = _balanced_and(conjuncts)        # balanced ⇒ shallow recursion
            for w in reversed(ws):
                body = Quantifier("∃", w, body)
            return body

        if self.op == "ge":
            return at_least(self.n.value)
        if self.op == "le":
            return Not(at_least(self.n.value + 1))
        return And(at_least(self.n.value), Not(at_least(self.n.value + 1)))

    def to_z3(self, env: Z3Env = None):
        """Lower to the distinct-witnesses encoding, then translate to Z3."""
        return self._expand().to_z3(env)

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Lower to the distinct-witnesses encoding, then render Prover9 syntax.

        The witnesses are fresh against every name of the whole node that is written, of every
        kind, compared case-folded, because Prover9 writes a variable in upper case: ``x0`` and
        ``X0`` are one variable there (see :meth:`Node.to_prover9`).
        """
        return self._expand().to_prover9()

    def to_tptp(self) -> str:
        """Lower to the distinct-witnesses encoding, then render TPTP syntax."""
        return self._expand().to_tptp()


@dataclass(frozen=True)
class Measure(Node):
    """A degree/measure term μ(entity, dimension): the degree to which ``entity`` has
    the gradable dimension ``dimension``.

    A first-class measure-function term, the clean argument for bare (standard-less)
    quantity comparatives — ``more water`` / ``taller`` become ``μ(x, dim) > μ(y, dim)``
    rather than a thin relational ``More(x, c)``. Both children are terms. On export it
    is the uninterpreted binary function ``measure(entity, dimension)`` (the ``μ`` glyph
    is ASCII-folded to ``measure`` so the first-order back-ends accept it), and ``>`` / ``<``
    over the resulting degrees use the back-end's ordering.
    """

    entity: Node
    dimension: Node

    def _tree_parts(self):
        """Return the μ label and the entity/dimension children."""
        return "μ", [self.entity, self.dimension]

    def to_dict(self):
        """Serialise to dict with serialised entity and dimension terms."""
        return {"_type": "Measure", "entity": self.entity.to_dict(),
                "dimension": self.dimension.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Measure from a dict produced by to_dict."""
        return Measure(Node.from_dict(d["entity"]), Node.from_dict(d["dimension"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to an uninterpreted binary Z3 function ``measure`` in sort S."""
        env = env or Z3Env()
        return env.get_func("measure", 2)(self.entity.to_z3(env), self.dimension.to_z3(env))

    def to_prover9(self) -> str:
        """Render as the Prover9 function ``measure(entity, dimension)``."""
        return f"measure({self.entity.to_prover9()}, {self.dimension.to_prover9()})"

    def to_tptp(self) -> str:
        """Render as the TPTP function ``measure(entity, dimension)``."""
        return f"measure({self.entity.to_tptp()},{self.dimension.to_tptp()})"

    def _tptp_symbol(self):
        """The function ``measure`` this node writes — the very symbol ``Function('measure', ...)`` is,
        so it collides with a differently-spelled ``Function('Measure', ...)`` and with nothing else."""
        return (_measure_symbol, "measure")


# Shared rejection message: a set-cardinality term is not first-order definable.
_NO_CARDINALITY_EXPORT = (
    "Cardinality terms (|{v : φ}|) denote set cardinality, a second-order notion "
    "with no first-order counterpart — counting comparisons such as 'more …​ than …' "
    "are not first-order definable. Keep the term at the AST level, or express a "
    "fixed-bound count with the Count quantifier (∃≥n / ∃≤n / ∃=n)."
)


@dataclass(frozen=True)
class Cardinality(Node):
    """A set-cardinality term ``|{v : φ}|``: how many ``v`` satisfy ``φ``.

    The first-class ``|S|`` term behind faithful counting comparisons — ``more votes
    than`` becomes ``|{v : Votes(x, v)}| > |{v : Votes(y, v)}|``. It BINDS ``variable``
    over the matrix ``formula``. Set cardinality is genuinely second-order, so it has
    no first-order export: :meth:`to_z3` / :meth:`to_prover9` / :meth:`to_tptp` reject.
    """

    variable: Variable
    formula: Node

    def _tree_parts(self):
        """Return the |v| cardinality label (with the bound variable) and the matrix."""
        return f"|{self.variable.name}|", [self.formula]

    def to_dict(self):
        """Serialise to dict with the bound variable and serialised matrix."""
        return {"_type": "Cardinality", "variable": self.variable.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Cardinality from a dict produced by to_dict."""
        return Cardinality(Node.from_dict(d["variable"]), Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: set cardinality has no first-order counterpart."""
        raise NotImplementedError(_NO_CARDINALITY_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: set cardinality has no first-order counterpart."""
        raise NotImplementedError(_NO_CARDINALITY_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: set cardinality has no first-order counterpart."""
        raise NotImplementedError(_NO_CARDINALITY_EXPORT)


@dataclass(frozen=True)
class Contrast(Node):
    """A concessive (contrastive) connective ``P Ⓒ Q`` — whereas / although / but.

    Truth-functionally identical to classical conjunction (concession is a discourse
    relation, not a truth-functional one), but kept as a distinct node so a front-end
    can preserve the contrast rather than flattening it to ∧. Exports therefore behave
    exactly like :class:`And`.
    """

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Contrast", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Contrast from a dict produced by to_dict."""
        return Contrast(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate like And (concession is truth-functionally conjunction)."""
        env = env or Z3Env()
        return z3.And(self.left.to_z3(env), self.right.to_z3(env))

    @_prover9_outermost
    def to_prover9(self) -> str:
        """Render like And, using the Prover9 ampersand operator."""
        return f"({self.left.to_prover9()} & {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render like And, using the TPTP ampersand operator."""
        return f"({self.left.to_tptp()} & {self.right.to_tptp()})"


# =========================
# Registry
# =========================

NODE_CLASSES = {
    "Variable": Variable, "Constant": Constant, "Number": Number,
    "Function": Function, "Atom": Atom, "Not": Not, "And": And,
    "Or": Or, "Xor": Xor, "Implies": Implies, "Iff": Iff,
    "Quantifier": Quantifier,
    "Count": Count, "Measure": Measure, "Cardinality": Cardinality,
}


# =========================
# Operator registry (self-registration)
# =========================
#
# A formula operator (a connective/modal that the precedence-driven renderers in
# _msfl_nodes.py format) registers ONE OperatorSpec here next to its class
# definition. The renderers then drive every regular operator from this registry,
# so adding an operator no longer means editing the central rendering tables.
#
# Each spec records, byte-for-byte, what the renderer emits:
#   - unicode: the glyph or prefix string for to_unicode_str (e.g. '¬', '□', 'K_').
#   - latex:   the LaTeX markup for to_latex, including any trailing space that
#              the current renderer emits (e.g. '\\lnot ', '\\Box ', 'K').
#   - fixity:  how the renderer arranges the operand(s) and the glyph.
#   - precedence: the formula precedence (higher binds tighter): 4 for prefix /
#              agent_prefix, 1 for binary_iff, 2 for binary_implies, 2.5 for
#              binary_until, 3 for level2.
#
# The "binders" (Quantifier, SortedQuantifier, SecondOrderQuantifier), Lambda and
# Application keep their explicit handling in the renderers and a small static
# precedence table — they are NOT regular operators and do NOT register here.

_VALID_FIXITIES = frozenset({
    "prefix", "agent_prefix",
    "binary_iff", "binary_implies", "binary_until",
    "level2",
})


@dataclass(frozen=True)
class OperatorSpec:
    """A renderer-facing description of one formula operator.

    name is the node class ``__name__`` (the renderers dispatch by class name).
    fixity is one of 'prefix', 'agent_prefix', 'binary_iff', 'binary_implies',
    'binary_until', 'level2'. unicode/latex are the EXACT strings the
    to_unicode_str / to_latex renderers emit for the operator's glyph or prefix
    (latex includes any trailing space). precedence is the formula precedence
    used for parenthesisation (a float; .5 values let an operator sit between two
    integer levels, as Until does at 2.5).
    """

    name: str
    fixity: str
    unicode: str
    latex: str
    precedence: float


# name -> OperatorSpec. Populated by register_operator as each node module is
# imported. The renderers in _msfl_nodes.py read this dict directly.
OPERATORS: Dict[str, OperatorSpec] = {}


def register_operator(node_class, fixity: str, unicode: str, latex: str,
                      precedence: float) -> OperatorSpec:
    """Register ``node_class`` as a renderable formula operator.

    Records an OperatorSpec under ``node_class.__name__`` in OPERATORS and adds
    the class to NODE_CLASSES (so from_dict/serialisation see it too). Safe to
    call more than once for the same class — the latest call overwrites the
    previous spec (idempotent / overwrite-safe). Returns the stored OperatorSpec.

    A node registered here is driven entirely by the central renderers via its
    spec, so no edit to _msfl_nodes.py is needed to render a new operator.
    """
    if fixity not in _VALID_FIXITIES:
        raise ValueError(
            f"register_operator: unknown fixity {fixity!r}; "
            f"expected one of {sorted(_VALID_FIXITIES)}"
        )
    name = node_class.__name__
    spec = OperatorSpec(name, fixity, unicode, latex, float(precedence))
    OPERATORS[name] = spec
    NODE_CLASSES[name] = node_class
    return spec


# Register the classical operators next to their class definitions above.
register_operator(Not, "prefix", "¬", "\\lnot ", 4)
register_operator(And, "level2", "∧", "\\land", 3)
register_operator(Or, "level2", "∨", "\\lor", 3)
register_operator(Xor, "level2", "⊕", "\\oplus", 3)
register_operator(Implies, "binary_implies", "→", "\\rightarrow", 2)
register_operator(Iff, "binary_iff", "↔", "\\leftrightarrow", 1)


# =========================
# Parser registry (self-assembling grammar)
# =========================
#
# A SECOND, parser-facing registry sits alongside the renderer registry above.
# Where OperatorSpec records how a node is *rendered*, ParserOp records how an
# operator is *parsed*: which grammar mode it belongs to, which precedence level
# it slots into, the grammar fragment it contributes, and the transform that
# turns the matched tokens into a Node. MSFLParser reads this registry per mode
# to build BOTH the Lark grammar string and the Transformer — so adding an
# operator is a registry entry in the operator's own module, with no edit to
# msflparser.py or the grammar skeleton.
#
# The same glyph maps to different nodes in different modes (∧ → And in FOL but
# WeakConjunction in MSFL), so registration is PER (mode, operator): a node may
# register several ParserOps, one per mode it appears in.
#
# Levels mirror the grammar's precedence layering (loosest first):
#   biimplication  the right-assoc ↔ rule              (one op per mode)
#   implication    the right-assoc → rule              (one op per mode)
#   until          the right-assoc Ⓤ rule (modal only) (one op per mode)
#   level2         the no-mixing same-level group ∧∨⊕⊗ (one only_X rule each)
#   prefix         ¬ and the prefix modal/temporal ops (the prefix rule's alts)
#   quantifier     ∀/∃ over a variable or predicate    (the quantifier alts)
#
# The shared term/atom/lambda/application layer is NOT registry-driven; it lives
# verbatim in the base template, identical across every mode (the only term-layer
# variation, sorted vs. plain constants, is selected by the SORTED flag below).

_VALID_PARSE_LEVELS = frozenset({
    "prefix", "level2", "implication", "biimplication", "until", "quantifier",
})

_VALID_MODES = frozenset({"fol", "msfol", "msfl", "fl", "modal", "second_order",
                          "higher_order",
                          "dependence", "linear", "lambek"})


@dataclass(frozen=True)
class ParserOp:
    """A parser-facing description of how one operator is parsed in one mode.

    mode      : the grammar mode this binding applies to (one of _VALID_MODES).
    level     : the precedence level it slots into (one of _VALID_PARSE_LEVELS).
    terminal_name : name of a named terminal to declare, or "" if the operator
                uses an inline string literal (the common case for the glyph
                connectives — kept inline so the error-path terminal patterns
                match the legacy grammars byte-for-byte).
    terminal_def  : the full terminal declaration line (e.g. 'BOX: "□"' or
                'KNOWS.5: /K_.../'), or "" when terminal_name is "".
    grammar  : the right-hand side of the grammar alternative this op contributes,
                already referencing the shared rule names (e.g. '"¬" prefix',
                'BOX prefix', or '(FORALL | EXISTS) VARIABLE prefix'). For a
                level2 op this is instead the glyph literal (e.g. '"∧"'), since
                level2 ops are spliced into the generated only_X / same_level_ops
                rules rather than contributing a free-standing alternative.
    rule_alias : the Lark rule alias (-> rule_alias) that names the parse node;
                the matching transform is attached to the assembled Transformer
                under this same name.
    transform  : function(items) -> Node implementing the alias's handler.
    node_class : the Node subclass produced (recorded for introspection/tests).
    only_name  : for level2 ops only, the generated only_X rule name (e.g.
                "only_and"); "" for every other level.
    """

    mode: str
    level: str
    terminal_name: str
    terminal_def: str
    grammar: str
    rule_alias: str
    transform: object
    node_class: object
    only_name: str = ""


# Append-only list of every parser binding, populated by register_parser_op as
# each node module imports. MSFLParser filters it by mode at construction time.
PARSER_OPS: List[ParserOp] = []


def register_parser_op(node_class, mode: str, level: str, rule_alias: str,
                       grammar: str, transform, *,
                       terminal_name: str = "", terminal_def: str = "",
                       only_name: str = "") -> ParserOp:
    """Register one parser binding for ``node_class`` in grammar mode ``mode``.

    Appends a ParserOp to PARSER_OPS. ``transform(items) -> Node`` is the handler
    Lark calls for the ``rule_alias`` reduction; ``grammar`` is the alternative's
    right-hand side (or, for a level2 op, the bare glyph literal). Named terminals
    are declared via ``terminal_name``/``terminal_def``; inline string operators
    leave both empty. Returns the stored ParserOp.

    This is additive to register_operator (which handles rendering): a fully
    self-describing operator calls both — register_operator for the renderers,
    register_parser_op (once per mode) for the parser.
    """
    if mode not in _VALID_MODES:
        raise ValueError(
            f"register_parser_op: unknown mode {mode!r}; "
            f"expected one of {sorted(_VALID_MODES)}"
        )
    if level not in _VALID_PARSE_LEVELS:
        raise ValueError(
            f"register_parser_op: unknown level {level!r}; "
            f"expected one of {sorted(_VALID_PARSE_LEVELS)}"
        )
    op = ParserOp(mode, level, terminal_name, terminal_def, grammar,
                  rule_alias, transform, node_class, only_name)
    PARSER_OPS.append(op)
    return op


def parser_ops_for_mode(mode: str) -> List[ParserOp]:
    """Return every registered ParserOp whose mode matches ``mode`` (in order)."""
    return [op for op in PARSER_OPS if op.mode == mode]


# ---------------------------------------------------------------------------
# Base grammar template
# ---------------------------------------------------------------------------
#
# ONE skeleton shared by every mode. The %%MARKERS%% are filled by
# build_grammar() from the mode's ParserOps. The structure: right-assoc ↔ and →,
# the optional Until sub-level, the no-mixing only_X same_level_ops group, the
# prefix level
# (¬ plus any prefix modal ops, then quantifier / atom / grouping), the tight
# quantifier binding (body is the prefix level), and the verbatim
# term/atom/lambda/application layer.
#
# Normalised internal rule names: the legacy grammars used negation /
# luk_negation / modal for the prefix level and biimplication / luk_biimplication
# (etc.) for the binary levels; because Lark inlines ?-rules and only the ->
# aliases name tree nodes, these internal names are irrelevant to the produced
# AST, so the template uses single uniform names (prefix, biimplication,
# implication, until, same_level_ops). The %%...%% markers:
#   %%TERMINAL_IMPORTS%%  the (...) list imported from .terminals (NUMBER,
#                          FORALL, EXISTS, LAMBDA — the identifier terminals
#                          PREDICATE/CONSTANT/NAME/VARIABLE/SORT are generated
#                          by fol/_identifiers.py and land in TERMINAL_DEFS
#                          instead; see that module's docstring for why)
#   %%TERMINAL_DEFS%%     the generated identifier terminals, followed by any
#                          extra named-terminal declarations (modal ops)
#   %%BIIMPL_OPS%%        the ↔ alternative(s)
#   %%IMPL_OPS%%          the → alternative(s)
#   %%IMPL_BODY%%         rule the → level reduces to: "until" or "same_level_ops"
#   %%UNTIL_BLOCK%%       the whole until rule (modal) or empty
#   %%LEVEL2_ALTS%%       the same_level_ops alternation members (only_X | … )
#   %%ONLY_RULES%%        the only_X rule definitions
#   %%PREFIX_OPS%%        the prefix alternatives contributed by ops (¬, modal …)
#   %%QUANT_OPS%%         the quantifier alternative(s)
#   %%CONST_ALTS%%        the atom_term constant rules (plain vs. sorted)

_BASE_GRAMMAR_TEMPLATE = '''\
%import .terminals (%%TERMINAL_IMPORTS%%)
%import common.WS
%%TERMINAL_DEFS%%
?start: formula

?formula: biimplication
    | lambda_
    | application_

?biimplication: implication
%%BIIMPL_OPS%%

?implication: %%IMPL_BODY%%
%%IMPL_OPS%%
%%UNTIL_BLOCK%%
?same_level_ops: %%LEVEL2_ALTS%%
%%ONLY_RULES%%
?prefix: %%PREFIX_OPS%%
    | quantifier
    | atom
    | "(" formula ")"
    | "[" formula "]"

?quantifier: %%QUANT_OPS%%

?atom: infix_predicate
     | PREDICATE "(" %%ATOM_ARGS%% ")"           -> atom_
     | PREDICATE                            -> atom0_
%%TRUTH_ATOMS%%
%%ATOM_EXTRA%%

?infix_predicate: term "<"  term            -> lt_
                | term ">"  term            -> gt_
                | term "="  term            -> eq_
                | term "≤" term            -> le_
                | term "≥" term            -> ge_
                | term "≠" term            -> ne_

?termlist: term ("," term)*

?term: sum

?sum: product
    | sum "+" product                       -> add_
    | sum "-" product                       -> sub_

?product: atom_term
    | product "*" atom_term                 -> mul_
    | product "/" atom_term                 -> div_

?atom_term: VARIABLE
    | NAME "(" termlist ")"                 -> function_
%%CONST_ALTS%%
    | NUMBER                                -> number_
%%TERM_EXTRA%%
    | "(" term ")"

lambda_: LAMBDA (VARIABLE | NAME | PREDICATE) "." formula
?app_arg: formula | atom_term
application_: "(" formula ")" "(" app_arg ")"

%ignore WS
'''


# The two constant-handling variants for the atom_term layer. Plain (FOL / FL /
# modal / second-order) treats a bare NAME as a Constant and c_-constants via
# const_; sorted (MSFOL / MSFL) requires a SORT annotation on each.
_CONST_ALTS_PLAIN = (
    "    | NAME\n"
    "    | CONSTANT                              -> const_"
)
_CONST_ALTS_SORTED = (
    "    | NAME SORT                             -> sorted_const_\n"
    "    | CONSTANT SORT                         -> sorted_const_"
)


# Per-mode grammar configuration that is NOT operator-specific: the terminal
# import list and whether constants are sorted. (The operators themselves come
# from the registry.)
#
# PREDICATE, CONSTANT, NAME, VARIABLE, and (for the sorted modes) SORT used to
# be listed here for %import, like NUMBER/FORALL/EXISTS/LAMBDA still are —
# they are generated instead now (see fol/_identifiers.py's module docstring
# for why) and spliced into %%TERMINAL_DEFS%% by build_grammar below, so this
# import list carries only the terminals that are still declared verbatim in
# fol/grammars/terminals.lark.
_MODE_TERMINAL_IMPORTS = {
    "fol":   "NUMBER, FORALL, EXISTS, LAMBDA",
    "msfol": "NUMBER, FORALL, EXISTS, LAMBDA",
    "msfl":  "NUMBER, FORALL, EXISTS, LAMBDA",
    "fl":    "NUMBER, FORALL, EXISTS, LAMBDA",
    "modal": "NUMBER, FORALL, EXISTS, LAMBDA",
    "second_order": "NUMBER, FORALL, EXISTS, LAMBDA",
    "third_order": "NUMBER, FORALL, EXISTS, LAMBDA",
    "third_order_modal": "NUMBER, FORALL, EXISTS, LAMBDA",
    "dependence": "NUMBER, FORALL, EXISTS, LAMBDA",
    "linear": "NUMBER, FORALL, EXISTS, LAMBDA",
    "lambek": "NUMBER, FORALL, EXISTS, LAMBDA",
}

_SORTED_MODES = frozenset({"msfol", "msfl"})


# Per-mode atom_term extensions that are NOT registry-driven (the term layer is the
# one hand-written part of the template). The classical unsorted modes (fol, modal,
# second_order) gain the measure term μ(entity, dimension) and the set-cardinality
# term |{v : φ}|; the matching FOLTransformer.measure_ / .cardinality_ handlers
# (base-class methods, so available in every mode) turn them into Measure /
# Cardinality nodes. All three share the plain (unsorted) term layer, so the same
# fragment applies verbatim; modal / second-order are included so a measure or
# cardinality term can appear under their operators (e.g. ◇(μ(x, height) > μ(y,
# height)) or ∃P (|{v : P(v)}| > c)). The SORTED modes msfol/msfl are absent because
# the |{v : φ}| binder would need a sort annotation; a mode absent from this map
# gets no extra term form.
_TERM_EXTRA_CLASSICAL = (
    '    | "μ" "(" termlist ")"                  -> measure_\n'
    '    | "|" "{" VARIABLE ":" formula "}" "|"  -> cardinality_'
)
# Sorted variant (MSFOL): the measure term is unchanged (its args are the mode's
# termlist), but the cardinality binder carries a sort annotation on the bound
# variable — |{v:Sort : φ}| → SortedCardinality — to stay consistent with MSFOL's
# rule that every binder is sorted.
_TERM_EXTRA_SORTED = (
    '    | "μ" "(" termlist ")"                       -> measure_\n'
    '    | "|" "{" VARIABLE SORT ":" formula "}" "|"  -> sorted_cardinality_'
)
_MODE_TERM_EXTRA = {
    "fol": _TERM_EXTRA_CLASSICAL,
    "modal": _TERM_EXTRA_CLASSICAL,
    "second_order": _TERM_EXTRA_CLASSICAL,
    "third_order": _TERM_EXTRA_CLASSICAL,
    "third_order_modal": _TERM_EXTRA_CLASSICAL,
    "msfol": _TERM_EXTRA_SORTED,
}


# Per-mode ARGUMENT layer for a predicate application. Every mode but the
# third-order ones takes an ordinary ``termlist``: a predicate's arguments
# are INDIVIDUALS, so ``P(x)`` is the whole story and a predicate name in
# argument position is a syntax error — which is exactly right for first-
# and second-order syntax, where ``∀P φ`` binds P as the HEAD of an
# application and never as an argument of one.
#
# The third-order modes widen that one position, and only that one: an
# argument may also be a PREDICATE name or a λ-abstraction, i.e. a PROPERTY.
# That is the whole syntactic content of "third order" — a predicate whose
# argument is itself a predicate (``Positive(G)``, ``Essence(G, x)``,
# ``Positive(λx. ¬G(x))``) — and it is why the level is not reachable by
# adding another quantifier to second-order syntax. The matching handlers are
# ``FOLTransformer.hoarglist`` (returns the argument list, exactly like
# ``termlist``) and ``LambdaTransformer.pred_arg_`` (builds the PredicateTerm;
# that one lives in msflparser.py because PredicateTerm is defined downstream
# of this module).
_MODE_ATOM_ARGS = {
    "third_order": "hoarglist",
    "third_order_modal": "hoarglist",
}
_ATOM_EXTRA_THIRD_ORDER = (
    'hoarglist: hoarg ("," hoarg)*\n'
    '\n'
    '?hoarg: term\n'
    '      | PREDICATE                            -> pred_arg_\n'
    '      | lambda_'
)
_MODE_ATOM_EXTRA = {
    "third_order": _ATOM_EXTRA_THIRD_ORDER,
    "third_order_modal": _ATOM_EXTRA_THIRD_ORDER,
}


# The two truth constants as atoms: ``⊤`` is the nullary atom ``$true`` and ``⊥`` the
# nullary atom ``$false`` (the atoms the TPTP reader builds), which is also what
# ``Node.to_unicode_str`` prints them as, so a formula that contains one reads back to
# itself. Every mode that has propositional atoms reads them. The two modes that do
# not are left alone: ``linear`` already gives the glyph ``⊤`` a meaning of its own
# (the additive unit of ``&``, a ``Top`` node, registered in ``_linear_nodes``) and
# ``lambek`` is a calculus of category types, with no propositional constants.
_TRUTH_ATOM_ALTS = (
    '     | "⊤"                                 -> true_\n'
    '     | "⊥"                                 -> false_\n'
)
_NO_TRUTH_ATOM_MODES = frozenset({"linear", "lambek"})


def build_grammar(mode: str) -> str:
    """Assemble the Lark grammar STRING for ``mode`` from the registry + template.

    Splices the mode's ParserOps into the base template's markers, preserving the
    exact precedence structure of the legacy hand-written grammar for that mode.
    Pure string assembly: no Lark object is built here (MSFLParser does that).
    """
    # Handler-only ops (empty grammar, e.g. sorted_const_ whose alternative lives
    # in the template's CONST_ALTS block) contribute a transform but no grammar
    # alternative, so they are excluded from every grammar-fragment join below.
    ops = [op for op in parser_ops_for_mode(mode) if op.grammar]

    # --- named-terminal declarations (modal operators; dedup, preserve order) ---
    seen_terms = set()
    term_defs = []
    for op in ops:
        if op.terminal_def and op.terminal_name not in seen_terms:
            seen_terms.add(op.terminal_name)
            term_defs.append(op.terminal_def)
    # The generated identifier terminals (PREDICATE, CONSTANT, NAME, VARIABLE,
    # and SORT for the sorted modes) go first, ahead of any modal/temporal
    # operator terminal — see fol/_identifiers.py's module docstring for why
    # they are generated rather than %import'd from terminals.lark.
    identifier_defs = _identifiers.terminal_block(include_sort=mode in _SORTED_MODES)
    terminal_defs = identifier_defs + (("\n".join(term_defs) + "\n") if term_defs else "")

    # --- until sub-level (modal only) ----------------------------------------
    # Determined first because it sets the implication body rule. ``op.grammar``
    # for an until op is just the operator glyph (literal or named terminal).
    until = [op for op in ops if op.level == "until"]
    if until:
        impl_body = "until"
        until_alts = "\n".join(
            f"    | same_level_ops {op.grammar} until            -> {op.rule_alias}"
            for op in until
        )
        until_block = f"\n?until: same_level_ops\n{until_alts}\n"
    else:
        impl_body = "same_level_ops"
        until_block = ""

    # --- biimplication (↔) — right-assoc; ``op.grammar`` is just the glyph ----
    biimpl = [op for op in ops if op.level == "biimplication"]
    biimpl_ops = "\n".join(
        f"    | implication {op.grammar} biimplication         -> {op.rule_alias}"
        for op in biimpl
    )

    # --- implication (→) — right-assoc; left operand is the implication body --
    impl = [op for op in ops if op.level == "implication"]
    impl_ops = "\n".join(
        f"    | {impl_body} {op.grammar} implication        -> {op.rule_alias}"
        for op in impl
    )

    # --- level2 (the no-mixing same_level_ops group) -------------------------
    level2 = [op for op in ops if op.level == "level2"]
    only_members = " | ".join(op.only_name for op in level2)
    level2_alts = f"{only_members} | prefix" if only_members else "prefix"
    only_rules = "\n".join(
        f"?{op.only_name}: prefix ({op.grammar} prefix)+         -> {op.rule_alias}"
        for op in level2
    )

    # --- prefix level (¬ and any prefix modal/temporal ops) ------------------
    prefix = [op for op in ops if op.level == "prefix"]
    prefix_ops = "\n    | ".join(f"{op.grammar}                     -> {op.rule_alias}" for op in prefix)

    # --- quantifier ----------------------------------------------------------
    quant = [op for op in ops if op.level == "quantifier"]
    quant_ops = "\n    | ".join(f"{op.grammar}   -> {op.rule_alias}" for op in quant)

    # --- term-layer constant handling ----------------------------------------
    const_alts = _CONST_ALTS_SORTED if mode in _SORTED_MODES else _CONST_ALTS_PLAIN

    # --- term-layer extensions (measure / cardinality; non-registry) ---------
    term_extra = _MODE_TERM_EXTRA.get(mode, "")

    grammar = _BASE_GRAMMAR_TEMPLATE
    grammar = grammar.replace("%%TERMINAL_IMPORTS%%", _MODE_TERMINAL_IMPORTS[mode])
    grammar = grammar.replace("%%TERMINAL_DEFS%%\n", terminal_defs)
    grammar = grammar.replace("%%BIIMPL_OPS%%", biimpl_ops)
    grammar = grammar.replace("%%IMPL_BODY%%", impl_body)
    grammar = grammar.replace("%%IMPL_OPS%%", impl_ops)
    grammar = grammar.replace("%%UNTIL_BLOCK%%\n", until_block)
    grammar = grammar.replace("%%LEVEL2_ALTS%%", level2_alts)
    grammar = grammar.replace("%%ONLY_RULES%%\n", (only_rules + "\n") if only_rules else "")
    # A mode may register NO quantifier ops (linear, lambek — propositional) or
    # NO prefix ops. Lark rejects a rule with an empty right-hand side, so the
    # empty level is excised from the template rather than left dangling: the
    # `| quantifier` alternative and the ?quantifier rule disappear together,
    # and an empty prefix level promotes the next alternative into first place.
    if not quant:
        grammar = grammar.replace("\n    | quantifier", "")
        grammar = grammar.replace("\n?quantifier: %%QUANT_OPS%%\n", "\n")
    if prefix_ops:
        grammar = grammar.replace("%%PREFIX_OPS%%", prefix_ops)
    else:
        grammar = grammar.replace("%%PREFIX_OPS%%\n    | ", "")
    grammar = grammar.replace("%%QUANT_OPS%%", quant_ops)
    grammar = grammar.replace("%%CONST_ALTS%%", const_alts)
    grammar = grammar.replace("%%TERM_EXTRA%%\n", (term_extra + "\n") if term_extra else "")
    # The predicate-application argument layer: ``termlist`` (individuals
    # only) for every mode but the third-order ones, which widen it to
    # ``hoarglist`` and bring the two extra rules along with it.
    grammar = grammar.replace("%%ATOM_ARGS%%", _MODE_ATOM_ARGS.get(mode, "termlist"))
    grammar = grammar.replace(
        "%%TRUTH_ATOMS%%\n", "" if mode in _NO_TRUTH_ATOM_MODES else _TRUTH_ATOM_ALTS)
    atom_extra = _MODE_ATOM_EXTRA.get(mode, "")
    grammar = grammar.replace("%%ATOM_EXTRA%%\n", (atom_extra + "\n") if atom_extra else "")
    return grammar


def build_transform_handlers(mode: str) -> Dict[str, object]:
    """Return ``{rule_alias: transform}`` for every ParserOp in ``mode``.

    MSFLParser attaches these to the assembled Transformer so each operator's
    parse handler lives next to its node definition, not in a hand-written
    Transformer subclass.
    """
    return {op.rule_alias: op.transform for op in parser_ops_for_mode(mode)}


# =========================
# Transformer
# =========================

class FOLTransformer(Transformer):
    """Transforms parsed tokens from Lark parser into AST nodes."""

    @staticmethod
    def _fold_binary(items, node_cls):
        """Left-fold a variable-length item list into nested binary nodes."""
        node = items[0]
        for item in items[1:]:
            node = node_cls(node, item)
        return node

    def atom0_(self, items):
        """Transform bare predicate symbol into a zero-arity Atom node."""
        pred = str(items[0])
        return Atom(pred, [])

    def true_(self, items):
        """Transform the glyph ``⊤`` into the truth constant, the atom ``$true``."""
        return Atom("$true", [])

    def false_(self, items):
        """Transform the glyph ``⊥`` into the falsity constant, the atom ``$false``."""
        return Atom("$false", [])

    def VARIABLE(self, items):
        """Transform variable token into Variable node."""
        return Variable(str(items))

    def NAME(self, items):
        """Transform name token into Constant node."""
        return Constant(str(items))

    def const_(self, items):
        """Transform a ``c_``-prefixed constant token into a Constant node."""
        return Constant(str(items[0]))

    def number_(self, items):
        """Transform numeric literal token into Number node."""
        try:
            return Number(_numeral_from_text(str(items[0])))
        except ValueError as exc:
            raise NumeralTextError(str(exc)) from None

    def function_(self, items):
        """Transform function application into Function node."""
        head = items[0]
        name = head.name if isinstance(head, Constant) else str(head)
        args = items[1:]
        if args and isinstance(args[0], list):
            args = args[0]
        return Function(name, args)

    def add_(self, items):
        """Transform addition into Function node."""
        left, right = items
        return Function("+", [left, right])

    def sub_(self, items):
        """Transform subtraction into Function node."""
        left, right = items
        return Function("-", [left, right])

    def mul_(self, items):
        """Transform multiplication into Function node."""
        left, right = items
        return Function("*", [left, right])

    def div_(self, items):
        """Transform division into Function node."""
        left, right = items
        return Function("/", [left, right])

    def atom_term(self, items):
        """Pass through atom term."""
        return items[0]

    def term(self, items):
        """Pass through term."""
        return items[0]

    def sum(self, items):
        """Pass through sum expression."""
        return items[0]

    def product(self, items):
        """Pass through product expression."""
        return items[0]

    def termlist(self, items):
        """Transform term list."""
        return items

    def hoarglist(self, items):
        """Transform a third-order argument list (individuals and/or properties).

        The third-order modes' counterpart to :meth:`termlist`: same contract
        (return the argument list for ``atom_`` to consume), but an entry may
        be a PredicateTerm or a Lambda as well as an ordinary term. Unlike
        ``?termlist`` this rule is NOT inlined by lark, so a one-argument
        application arrives here as a one-element list rather than as a bare
        node — ``atom_`` accepts either.
        """
        return items

    def infix_predicate(self, items):
        """Pass through infix predicate."""
        return items[0]

    def atom(self, items):
        """Pass through atom."""
        return items[0]

    def atom_(self, items):
        """Transform predicate application into Atom node."""
        pred = str(items[0])
        if not isinstance(items[1], list):
            args = [items[1]]
        else:
            args = items[1]
        return Atom(pred, args)

    def lt_(self, items):
        """Transform less-than comparison into Atom node."""
        left, right = items
        return Atom("<", [left, right])

    def gt_(self, items):
        """Transform greater-than comparison into Atom node."""
        left, right = items
        return Atom(">", [left, right])

    def eq_(self, items):
        """Transform equality comparison into Atom node."""
        left, right = items
        return Atom("=", [left, right])

    def le_(self, items):
        """Transform less-than-or-equal comparison into Atom node."""
        left, right = items
        return Atom("≤", [left, right])

    def ge_(self, items):
        """Transform greater-than-or-equal comparison into Atom node."""
        left, right = items
        return Atom("≥", [left, right])

    def ne_(self, items):
        """Transform not-equal comparison into Atom node."""
        left, right = items
        return Atom("≠", [left, right])

    def not_(self, items):
        """Transform negation into Not node."""
        return Not(items[0])

    def and_(self, items):
        """Transform conjunction into And node."""
        return self._fold_binary(items, And)

    def or_(self, items):
        """Transform disjunction into Or node."""
        return self._fold_binary(items, Or)

    def xor_(self, items):
        """Transform exclusive or into Xor node."""
        return self._fold_binary(items, Xor)

    def implies_(self, items):
        """Transform implication into Implies node."""
        return Implies(items[0], items[1])

    def iff_(self, items):
        """Transform biconditional into Iff node."""
        return Iff(items[0], items[1])

    def quantifier_(self, items):
        """Transform quantifier expression into Quantifier node."""
        quant = items[0]
        var = items[1]
        formula = items[2]
        return Quantifier(str(quant), var, formula)

    def measure_(self, items):
        """Transform μ(entity, dimension) into a Measure term node (exactly 2 args)."""
        args = items[0] if items and isinstance(items[0], list) else list(items)
        if len(args) != 2:
            raise ValueError(
                f"μ(...) takes exactly two arguments (entity, dimension); got {len(args)}.")
        return Measure(args[0], args[1])

    def cardinality_(self, items):
        """Transform |{v : φ}| into a Cardinality term node binding v over φ."""
        return Cardinality(items[0], items[1])


# =========================
# Parser registration (FOL / MSFOL connectives + quantifier)
# =========================
#
# Self-register the classical connectives and the unsorted quantifier with the
# parser registry. Each transform mirrors the corresponding FOLTransformer method
# exactly (same items[…] handling, same node), so the assembled parser produces
# byte-identical ASTs. The connectives shared by FOL and MSFOL (∧ ∨ ¬ → ↔) and
# the quantifier register once per mode they appear in; FOL additionally has ⊕
# (Xor). The sorted quantifier and the Łukasiewicz/MSFL bindings live in
# _msfl_nodes.py; the modal/second-order bindings in their own modules.

def _fold_binary(items, node_cls):
    """Left-fold a variable-length item list into nested binary nodes (registry copy)."""
    node = items[0]
    for item in items[1:]:
        node = node_cls(node, item)
    return node


# Classical ∧ ∨ ¬ → ↔ are shared by FOL, MSFOL, modal, and second-order modes;
# ⊕ (Xor) by every CLASSICAL mode — FOL, MSFOL, modal, and second-order (the glyph ⊕
# is the Łukasiewicz strong disjunction in the fuzzy modes, so Xor stays out of those).
# The unsorted quantifier is shared by FOL, modal, and second-order (the sorted modes
# use SortedQuantifier). Each connective registers once per mode with the SAME grammar
# fragment and transform, so the assembled parser produces byte-identical ASTs.
_CLASSICAL_MODES = ("fol", "msfol", "modal", "second_order")
_XOR_MODES = ("fol", "msfol", "modal", "second_order")
_UNSORTED_QUANT_MODES = ("fol", "modal", "second_order")


def _quantifier_transform(items):
    """Build an unsorted Quantifier from [FORALL/EXISTS token, Variable, body]."""
    return Quantifier(str(items[0]), items[1], items[2])


# --- prefix: ¬ (Not) ---
for _m in _CLASSICAL_MODES:
    register_parser_op(Not, _m, "prefix", "not_", '"¬" prefix',
                       lambda items: Not(items[0]))

# --- level2: ∧ ∨ (And, Or) everywhere classical; ⊕ (Xor) where allowed ---
for _m in _CLASSICAL_MODES:
    register_parser_op(And, _m, "level2", "and_", '"∧"',
                       lambda items: _fold_binary(items, And), only_name="only_and")
    register_parser_op(Or, _m, "level2", "or_", '"∨"',
                       lambda items: _fold_binary(items, Or), only_name="only_or")
for _m in _XOR_MODES:
    register_parser_op(Xor, _m, "level2", "xor_", '"⊕"',
                       lambda items: _fold_binary(items, Xor), only_name="only_xor")

# --- implication: → (Implies) ---
# For binary levels (implication / biimplication / until) the ``grammar`` field
# holds JUST the operator glyph; build_grammar assembles the full right-assoc
# rule from it (the operand rule names are fixed by the level structure). This
# lets the → rule's left operand follow the mode's implication body (same_level_ops
# normally, or until in modal mode) without a mode-specific fragment.
for _m in _CLASSICAL_MODES:
    register_parser_op(Implies, _m, "implication", "implies_", '"→"',
                       lambda items: Implies(items[0], items[1]))

# --- biimplication: ↔ (Iff) ---
for _m in _CLASSICAL_MODES:
    register_parser_op(Iff, _m, "biimplication", "iff_", '"↔"',
                       lambda items: Iff(items[0], items[1]))

# --- quantifier: unsorted ∀x / ∃x (Quantifier) ---
for _m in _UNSORTED_QUANT_MODES:
    register_parser_op(Quantifier, _m, "quantifier", "quantifier_",
                       "(FORALL | EXISTS) VARIABLE prefix", _quantifier_transform)


# Modes that accept the NL / CCG translation-target nodes (Count, Contrast, and —
# via _MODE_TERM_EXTRA below — the Measure / Cardinality terms). These are the
# CLASSICAL, UNSORTED modes — every mode that is a conservative extension of
# classical unsorted FOL and therefore reads the constructs with IDENTICAL
# semantics: plain fol, modal (fol + modal operators), and second-order (fol +
# quantifiers over predicate variables). A CCG-derived form routinely nests one of
# these fol-level constructs under a modal or second-order operator — e.g. "every
# professor believes at least three students will pass" is Believes_x(∃≥3 y …) —
# so registering the same grammar fragment + transform across the family lets the
# whole mixed formula parse (and round-trip) as a single string, not only as a
# hand-built AST. (The SORTED classical modes msfol/msfl need sort-annotated
# binders, and the fuzzy modes fl/msfl reinterpret the connectives and reject
# comparison atoms, so neither is included here.)
_NL_NODE_MODES = ("fol", "modal", "second_order")


# --- counting quantifier: ∃≥n / ∃≤n / ∃=n (Count), fol + modal modes ---
# COUNTOP is one named terminal matching all three glyphs (∃ followed by ≥/≤/=),
# at lexer priority 5 so it wins over EXISTS (∃) on the longer match; the matched
# glyph in items[0] selects the op code. The bound NUMBER must be a non-negative
# integer: the terminal reads a sign and a decimal point because TERMS need them
# (``P(-3)``, ``x < 2.5``), so ``∃≥-2`` and ``∃≥2.5`` reach this rule and are
# refused here, as a parse error (see CountBoundError).
class CountBoundError(ParsingError):
    """A counting quantifier whose bound is not a non-negative integer.

    Subclasses ParsingError, so the CLI, ``api.parse_any`` and every caller that
    catches the parser's error type report it as the one-line SYNTAX_ERROR it is
    (the parser re-raises a ParsingError a transformer handler produced instead
    of lark's opaque VisitError, as it does for ConflictingArityError). It is
    constructed directly, not from a Lark exception, so it sets its own message.
    """

    def __init__(self, glyph: str, bound: str, column=None):
        where = f" at position {column}" if isinstance(column, int) and column >= 0 else ""
        message = (
            f"SYNTAX_ERROR: the bound of a counting quantifier must be a "
            f"non-negative integer, got {bound!r}{where} after {glyph!r}. A count "
            f"is a whole number of witnesses: write it without a sign or a "
            f"decimal point, e.g. {glyph}2.")
        self.args = (message,)

    def __str__(self):
        return self.args[0]


def _count_bound(glyph_token, number_token) -> int:
    """The integer a counting quantifier's bound token stands for.

    A bound is an unsigned numeral: a sign makes it a CountBoundError whatever
    the number is (``-2``, and also ``-0``, which equals 0 as a number but is not
    the numeral ``0``), and so does a decimal point (``2.5``, and also ``2.0``).
    """
    text = str(number_token)
    if "." not in text and not text.startswith(("-", "+")):
        return int(text)
    raise CountBoundError(str(glyph_token), text, getattr(number_token, "column", None))


def _count_transform(items):
    """Build a Count from [COUNTOP glyph token, NUMBER token, Variable, body]."""
    op = _COUNT_TOKEN_TO_OP[str(items[0])]
    return Count(op, Number(_count_bound(items[0], items[1])), items[2], items[3])


for _m in _NL_NODE_MODES:
    register_parser_op(Count, _m, "quantifier", "count_",
                       "COUNTOP NUMBER VARIABLE prefix", _count_transform,
                       terminal_name="COUNTOP", terminal_def="COUNTOP.5: /∃[≥≤=]/")


# --- concessive connective: P Ⓒ Q (Contrast) — every CLASSICAL mode ---
# A regular level2 operator (same precedence as ∧ ∨ ⊕): self-registers with the
# renderers and the parser, so no renderer branch is needed (it dispatches on
# spec.fixity == "level2"). Truth-functionally conjunction; kept distinct in the AST.
# Unlike the counting binder it needs no sort annotation, so it drops into the sorted
# MSFOL mode too — hence the classical-mode list rather than _NL_NODE_MODES.
_CONTRAST_MODES = ("fol", "modal", "second_order", "msfol")
register_operator(Contrast, "level2", "Ⓒ", "\\mathbin{\\mathsf{C}}", 3)
for _m in _CONTRAST_MODES:
    register_parser_op(Contrast, _m, "level2", "contrast_", '"Ⓒ"',
                       lambda items: _fold_binary(items, Contrast),
                       only_name="only_contrast")
