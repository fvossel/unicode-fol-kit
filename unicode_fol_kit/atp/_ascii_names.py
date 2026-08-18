"""Shared ASCII-identifier sanitisation for the ASCII-only export surfaces:
TPTP (:mod:`atp._tptp_problem`), Prover9 (:mod:`atp.prover9_entailment`), and
SMT-LIB2/cvc5 (:mod:`atp.cvc5_backend`).

WHY THIS IS NOT :mod:`fol.sanitize`
-------------------------------------
:mod:`fol.sanitize`'s :class:`~fol.sanitize.NameMapping` already solves
exactly this shape of problem — an injective, whole-problem-consistent
rewrite to legal tokens, with a reverse mapping back to the originals — but
its target legality is the kit's OWN ``MSFLParser`` grammar, not any of
these export formats'. The two disagree in a way that matters: a single-
letter constant such as ``a`` is not a legal bare ``NAME`` token in the
kit's own grammar (it would re-lex as a ``VARIABLE``), so
``NameMapping.for_constant("a")`` rewrites it to ``c_a`` — but ``a`` is
already a perfectly legal TPTP ``lower_word`` / Prover9 ``NAME`` /
SMT-LIB2 simple symbol, and an exporter that "fixed" it anyway would
silently change the output of every formula using a short constant,
breaking the "already-legal names pass through byte-identical" guarantee
these export entry points make to their callers (see each of this module's
callers' own module docstrings). So each target format gets its OWN
legality test and its own synthesis rule for the names that fail it, built
from the primitives below — the same INJECTIVE / whole-problem-consistent
/ reversible SHAPE :class:`~fol.sanitize.NameMapping` uses (a shared
reservation set, numeric-suffix de-collision, a flat reverse dict), just
parametrised per format instead of reusing that class's kit-specific
methods directly.

:func:`ascii_safe_base` is the one piece every target genuinely shares:
transliterating non-ASCII characters via
:func:`unicode_fol_kit.fol._fol_nodes.constant_name_to_ascii` (the same
Greek-letter-name / reversible ``uXXXX``-escape rule
:meth:`~fol.nodes.Constant.to_tptp` and :meth:`~fol.nodes.Constant.to_prover9`
already use) and guaranteeing the result does not start with a digit or come
out empty.
"""

import re
from typing import Callable, Dict, Set

from ..fol._fol_nodes import constant_name_to_ascii

__all__ = ["ascii_safe_base", "reserve_rendered", "reverse_map_text"]


def ascii_safe_base(name: str, prefix: str) -> str:
    """Transliterate ``name`` to ASCII and ensure a non-digit-leading result.

    Reuses :func:`constant_name_to_ascii` (ASCII passes through, a Greek
    letter becomes its spelled name, anything else non-ASCII becomes a
    reversible ``uXXXX`` escape) — every one of those three outcomes starts
    with a letter, so the ONLY way the result can still start with a digit
    (or be empty) is if ``name`` itself was already plain ASCII and
    digit-leading (transliteration is a no-op on it). ``prefix`` is
    prepended in that case; it is also prepended to an empty transliteration
    (``name`` was empty, or every character became... nothing — not reached
    by any of :func:`constant_name_to_ascii`'s cases today, but kept as an
    honest fallback rather than an assumption).
    """
    ascii_name = constant_name_to_ascii(name)
    if not ascii_name or ascii_name[0].isdigit():
        ascii_name = prefix + ascii_name
    return ascii_name


def reserve_rendered(base: str, used: Set[str],
                     render: Callable[[str], str] = lambda s: s) -> str:
    """Return a token starting from ``base`` whose ``render(...)`` form is not
    yet in ``used``, reserving that rendered form; mirrors
    :meth:`fol.sanitize.NameMapping._reserve`'s numeric-suffix scheme
    (``base``, then ``base2``, ``base3``, ...) but de-collides on the
    RENDERED form (what actually appears in the exported text — e.g. after
    TPTP's first-letter fold) rather than on ``base`` itself, since two
    different raw candidates can still render to the same text (``Foo2`` and
    ``foo2`` both fold to ``foo2``). ``render`` defaults to the identity
    (Prover9 and SMT-LIB2 render every accepted token verbatim; only TPTP
    needs a non-identity ``render``).
    """
    candidate = base
    i = 2
    while render(candidate) in used:
        candidate = f"{base}{i}"
        i += 1
    used.add(render(candidate))
    return candidate


def reverse_map_text(text: str, *reverse_dicts: Dict[str, str]) -> str:
    """Replace whole-token occurrences of a sanitised identifier in free
    text with its original kit-level name.

    Used for the free-text side of the Rückweg (R3's "Erklärungstexte") —
    a prover's raw stdout excerpt, an error detail string, and similar —
    where the identifiers of interest sit inside a larger human-readable
    string rather than in a parsed :class:`~fol.nodes.Node`. Matching is by
    whole token (regex word boundaries) so a sanitised name that happens to
    be a substring of something else (another identifier, a longer word in
    surrounding prose) is never partially rewritten; the first
    ``reverse_dicts`` entry to contain a given token wins, and tokens are
    tried longest-first so one sanitised name that is itself a prefix of
    another is not matched short. Returns ``text`` unchanged if every dict
    is empty (the common case: nothing needed sanitising, so nothing needs
    reversing) or if ``text`` is empty.
    """
    combined: Dict[str, str] = {}
    for d in reverse_dicts:
        for token, original in d.items():
            combined.setdefault(token, original)
    if not combined or not text:
        return text
    pattern = re.compile(
        r"\b(" + "|".join(re.escape(t) for t in sorted(combined, key=len, reverse=True)) + r")\b"
    )
    return pattern.sub(lambda m: combined[m.group(1)], text)
