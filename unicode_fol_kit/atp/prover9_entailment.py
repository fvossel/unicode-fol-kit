"""Entailment checking via the Prover9 theorem prover (LADR backend).

Builds a Prover9 ``.in`` file (``set(prolog_style_variables)``, one
``formulas(assumptions)`` list of premises, one ``formulas(goals)`` list
holding the conclusion) and looks for ``THEOREM PROVED`` in Prover9's stdout.

**ASCII/legality sanitisation (problem-level seam).** ``Node.to_prover9()``
renders a predicate/function name completely verbatim (no transliteration,
no case change at all) and a Constant name transliterated to ASCII
(:func:`~unicode_fol_kit.fol._fol_nodes.constant_name_to_ascii`) but without
fixing a digit-leading result. Prover9's own reader grammar for a symbol
token is ``NAME: /[A-Za-z_][A-Za-z0-9_]*/`` (see
:data:`unicode_fol_kit.fol.prover9_input`'s ``NAME`` terminal) — a
non-ASCII character or a digit-leading name is not a legal token there at
all. Neither gap could be reached before the toolkit's own identifier
grammar was widened to accept Unicode letters and digit-leading names; both
can now. Exactly like :mod:`atp._tptp_problem`, the fix has to live at
problem level, not inside ``Node.to_prover9()`` itself (see that module's
docstring for the full reasoning — independent per-node renaming loses
injectivity and never reaches a caller that needs to invert it):
:func:`_sanitize_for_prover9` walks every premise and the conclusion
TOGETHER, replaces only the names that are not already Prover9-legal with
an ASCII, non-digit-leading, whole-problem-injective replacement, and
returns a :class:`Prover9NameMap` recording exactly what was renamed. An
already-legal name — including one that is upper-case-initial, such as the
kit's own predicate convention, which :func:`test_export_fixes.py
<unicode_fol_kit>`'s ``Atom("Rain", []).to_prover9() == "Rain"`` pins as
existing, deliberate, untouched behaviour — passes through completely
unchanged, so this sanitisation step never alters the output for a formula
this module was already exporting correctly.

There is currently no Prover9 "detailed" route reading a proof or
countermodel back out of Prover9's own output (:func:`check_logical_entailment`
and :class:`~unicode_fol_kit.atp.protocol.Prover9Backend` both report a bare
``bool``/PROVED-or-UNKNOWN verdict, nothing that carries a Prover9-chosen
symbol name back to the caller) — so there is no Rückweg to wire up here
today. :class:`Prover9NameMap` still exists and is still returned by
:func:`generate_prover9_input_with_mapping` (mirroring
:mod:`atp._tptp_problem`'s ``..._with_mapping``/plain-wrapper split) so a
future detailed route has the same reversible mapping available without
redesigning this module.
"""

import os
import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from typing import Dict, List, Tuple

from ..fol.nodes import Atom, Constant, Function, Node
from ._ascii_names import ascii_safe_base, reserve_rendered

__all__ = ["check_logical_entailment", "Prover9NameMap",
           "generate_prover9_input_with_mapping"]


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — see the module docstring.
# ---------------------------------------------------------------------------

# A raw kit-level name that is ALREADY a legal Prover9 NAME token (matches
# fol/prover9_input.py's own ``NAME: /[A-Za-z_][A-Za-z0-9_]*/`` terminal) and
# is pure ASCII (Node.to_prover9 never transliterates a predicate/function
# name, only a Constant, and even that doesn't fix digit-leading — see the
# module docstring). Names the widened parser can now produce never contain
# anything outside unicode letters/digits/underscore/combining marks, so
# this is the exact complement of "needs a replacement".
_PROVER9_SAFE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _is_prover9_safe(name: str) -> bool:
    return bool(name) and name.isascii() and bool(_PROVER9_SAFE_RE.fullmatch(name))


def _lowercase_initial(base: str) -> str:
    """Force a lowercase-initial result for a SYNTHESISED (previously
    illegal) name — never applied to an already-legal passthrough name, so
    this never touches the kit's own upper-case-initial predicate
    convention (see the module docstring's ``Atom("Rain", [])`` note).
    Lowercase-initial avoids Prover9's own ``prolog_style_variables``
    ambiguity (an upper-case- or underscore-initial symbol reads as a
    VARIABLE) for names this module is choosing fresh, rather than
    reproducing that ambiguity for brand-new tokens nobody has to preserve
    the case of.
    """
    return base[0].lower() + base[1:] if base else base


@dataclass
class Prover9NameMap:
    """The renamings :func:`_sanitize_for_prover9` chose for one problem.

    A single FLAT namespace across predicate/function/constant names (unlike
    :mod:`atp._tptp_problem`'s predicate-vs-term split): Prover9's own export
    never case-folds, so an already-legal name can never collide with
    another already-legal name the way TPTP's first-letter fold can, and
    being conservative about a SYNTHESISED replacement never colliding with
    ANY other name in the problem — predicate, function, or constant alike —
    costs nothing but an occasional extra numeric suffix. ``mapping`` is the
    original-kit-name -> token dict; an original name that was already
    legal maps to itself.
    """

    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _pending: List[str] = field(default_factory=list)

    def collect(self, name: str) -> None:
        """First pass: register `name`; an already-legal name is reserved
        immediately (order-independent — see
        :class:`~atp._tptp_problem._Renamer`'s docstring for why a
        synthesised name's collision-avoidance must not depend on which
        already-legal name it happens to be processed before or after)."""
        if name in self.mapping or name in self._pending:
            return
        if _is_prover9_safe(name):
            self.used.add(name)
            self.mapping[name] = name
        else:
            self._pending.append(name)

    def finalize(self) -> None:
        """Second pass: synthesise a token for every queued name, now that
        every already-legal name in the WHOLE problem is reserved."""
        for name in self._pending:
            base = _lowercase_initial(ascii_safe_base(name, "s"))
            token = reserve_rendered(base, self.used)
            self.mapping[name] = token
        self._pending = []

    def get(self, name: str) -> str:
        return self.mapping[name]

    def reverse(self) -> Dict[str, str]:
        """Flat token -> original dict (Prover9 never case-folds, so the
        token stored in ``mapping`` is exactly what would come back from any
        future reader of Prover9's own output — no fold/cap asymmetry to
        account for, unlike TPTP's predicate namespace)."""
        return {v: k for k, v in self.mapping.items()}


def _sanitize_node_for_prover9(node: Node, names: Prover9NameMap) -> Node:
    """Rebuild ``node`` with every non-Prover9-legal symbol name replaced.

    Mirrors :func:`atp._tptp_problem._sanitize_node_for_tptp`'s structural
    recursion (``Node.map_children`` for everything that is not itself an
    Atom/Function/Constant); an already-legal name comes back as the exact
    same string, so ``Node.to_prover9()`` on the result is byte-identical to
    ``Node.to_prover9()`` on the original wherever every name involved was
    already legal (R1).
    """
    if isinstance(node, Atom):
        if node.predicate in Atom.INFIX_PREDS_P9:
            pred = node.predicate
        else:
            pred = names.get(node.predicate)
        return Atom(pred, [_sanitize_node_for_prover9(a, names) for a in node.args])
    if isinstance(node, Function):
        if node.name in Function.INFIX_OPS:
            name = node.name
        else:
            name = names.get(node.name)
        return Function(name, [_sanitize_node_for_prover9(a, names) for a in node.args])
    if isinstance(node, Constant):
        return Constant(names.get(node.name))
    return node.map_children(lambda c: _sanitize_node_for_prover9(c, names))


def _collect_names_for_prover9(node: Node, names: Prover9NameMap) -> None:
    """First pass (see :meth:`Prover9NameMap.collect`): register every
    predicate/function/constant name ``node`` (and its descendants) uses,
    without rewriting anything yet."""
    for n in node.walk():
        if isinstance(n, Atom):
            if n.predicate not in Atom.INFIX_PREDS_P9:
                names.collect(n.predicate)
        elif isinstance(n, Function):
            if n.name not in Function.INFIX_OPS:
                names.collect(n.name)
        elif isinstance(n, Constant):
            names.collect(n.name)


def _sanitize_for_prover9(formulas: List[Node]) -> Tuple[List[Node], Prover9NameMap]:
    """Sanitise every formula's predicate/function/constant names for Prover9.

    Returns ``(sanitised_formulas, mapping)`` — see the module docstring.
    The single namespace is shared across ALL of ``formulas``, so the same
    original name maps to the same token everywhere (R2), and a synthesised
    token can never collide with any name anywhere in the problem,
    regardless of where each one appears
    (:meth:`Prover9NameMap.collect`/:meth:`~Prover9NameMap.finalize`'s
    two-pass split — see :class:`atp._tptp_problem._Renamer`'s docstring for
    why a single combined pass would be order-dependent).
    """
    names = Prover9NameMap()
    for f in formulas:
        _collect_names_for_prover9(f, names)
    names.finalize()
    sanitised = [_sanitize_node_for_prover9(f, names) for f in formulas]
    return sanitised, names


def generate_prover9_input_with_mapping(premises: List[Node], conclusion: Node
                                        ) -> Tuple[str, Prover9NameMap]:
    """Like :func:`_generate_prover9_input`, but also returns the
    :class:`Prover9NameMap` recording every ASCII-legality rename applied.

    No current caller in this module reads a Prover9-chosen symbol name back
    out of its output (see the module docstring), but this is the function
    a future "detailed" Prover9 route would call instead of
    :func:`_generate_prover9_input`, exactly the way
    :mod:`atp.vampire_entailment`'s detailed route uses
    :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`.
    """
    sanitised, mapping = _sanitize_for_prover9(list(premises) + [conclusion])
    sanitised_premises, sanitised_conclusion = sanitised[:-1], sanitised[-1]

    lines = []
    lines.append("set(prolog_style_variables).")
    lines.append("set(auto_denials).")
    lines.append("clear(print_initial_clauses).")
    lines.append("clear(print_kept).")
    lines.append("clear(print_given).")
    lines.append("")

    lines.append("formulas(assumptions).")
    for premise in sanitised_premises:
        lines.append(f"  {premise.to_prover9()}.")
    lines.append("end_of_list.")
    lines.append("")

    lines.append("formulas(goals).")
    lines.append(f"  {sanitised_conclusion.to_prover9()}.")
    lines.append("end_of_list.")

    return "\n".join(lines), mapping


def _generate_prover9_input(premises: List[Node], conclusion: Node) -> str:
    """
    Generates a Prover9 input string from given premises and conclusion.

    Every predicate/function/constant name is first made Prover9-ASCII-legal
    (see the module docstring's sanitisation section) — a name that was
    already legal renders byte-identically to before that step existed.

    Args:
        premises (list[Node]): List of premise formulas in FOL.
        conclusion (Node): Conclusion formula in FOL.

    Returns:
        str: Formatted Prover9 input string.
    """
    text, _mapping = generate_prover9_input_with_mapping(premises, conclusion)
    return text


def _run_prover9(input: str, prover9_path: str, timeout: int = 30) -> bool:
    """Run the prover9 command line tool."""

    with tempfile.NamedTemporaryFile(mode='w', suffix='.in', delete=False) as temp_file:
        temp_file.write(input)
        temp_filename = temp_file.name

    try:
        result = subprocess.run(
            [prover9_path, '-f', temp_filename],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        success = "THEOREM PROVED" in result.stdout
    except subprocess.TimeoutExpired:
        success = False
    finally:
        # Always remove the temp file, even when subprocess.run raises (e.g.
        # FileNotFoundError for a wrong prover9_path); the exception still
        # propagates to the caller.
        try:
            os.unlink(temp_filename)
        except OSError:
            pass

    return success


def check_logical_entailment(premises: list[Node], conclusion: Node, prover9_path: str) -> bool:
    """Checks if a conclusion entails from the defined premises by using prover9."""

    prover9_input = _generate_prover9_input(premises, conclusion)
    success = _run_prover9(prover9_input, prover9_path)
    return success
