"""Inductive logic programming: structures in, a learning task out.

The other end of :mod:`unicode_fol_kit.fol.prolog_input`. That module reads a
learner's answer; this one writes the learner's question — the background
knowledge, examples and language bias an ILP system (Popper, Aleph, Metagol)
needs, built from the very same
:class:`~unicode_fol_kit.semantics.structures.FiniteStructure` objects the
kit's model checker evaluates against. The loop closes:

    structure --IlpTask--> Prolog task --learner--> clause
        --clause_to_formula--> kit formula --model checker--> verdicts

Why a module and not a script
-----------------------------
Because two encoding mistakes are easy to make, impossible to see in the
output, and both produce a hypothesis that scores **precision 1.00 and means
nothing**. Both were made while building this kit's own pre-trial, and both
are now structurally impossible here rather than written down as advice:

**1. Example-local individual names.** A structure names its individuals
locally — every molecule has a ``c1``. Emit those raw and the same constant
denotes a different thing in each example, so a learner can join *across*
examples. It will:

.. code-block:: prolog

   amide(A) :- bSINGLE(A,B,C), n(D,B), bDOUBLE(D,E,C), bDOUBLE(A,C,E).

scored perfectly by hopping between molecules through a shared atom name.
:class:`IlpTask` prefixes every individual with its example and **refuses the
task** if two ``(example, individual)`` pairs would still collide — the check
is in the constructor, so a colliding task cannot be written at all.

**2. The example argument on every predicate.** Carry the example everywhere
(``c(M,X)``, ``bond(M,X,Y)``) and the learner can introduce a *second* example
variable and connect through it. The resulting clause is not a statement about
one structure, and cannot be translated into one. Here the example argument
exists on the membership predicate **alone** — the emitter has no way to put
it anywhere else — and :func:`clause_to_formula` refuses, on the way back, any
clause in which the example variable survives dropping the membership atoms.

A third guard falls out of the same reasoning: a **0-ary** background
predicate cannot be attached to an example at all, so it would hold globally
across every example. It is excluded from an inferred vocabulary (visibly, via
:attr:`IlpTask.excluded_predicates` and a comment in the emitted file) and
refused if named explicitly.

What this module does NOT do
----------------------------
It does not run a learner. Popper needs SWI-Prolog and, from v4, ``janus_swi``
— a dependency the kit does not take on for a file format. It writes the three
files Popper reads (``bk.pl``, ``exs.pl``, ``bias.pl``), and reads back the
text a learner prints. Everything in between is the learner's business.

It also does not decide whether your task is a *good* one. It does offer the
one check that has to happen first: :func:`check_separation` asks whether a
reference formula actually separates the two example sets under the kit's own
model checker. If it does not, the task is broken and no answer from any
learner would have meant anything.

    >>> from unicode_fol_kit.semantics import FiniteStructure
    >>> from unicode_fol_kit.ilp import IlpTask, Example
    >>> yes = FiniteStructure(domain=("a1",), extensions={("p", 1): [("a1",)]})
    >>> no = FiniteStructure(domain=("a1",), extensions={("p", 1): []})
    >>> task = IlpTask("target", [Example("e1", yes, True),
    ...                           Example("e2", no, False)])
    >>> print(task.examples_text())
    pos(target(e1)).
    neg(target(e2)).
    <BLANKLINE>
"""

from .task import (
    Example, IlpTask, IlpEncodingError, task_from_structures, to_prolog_atom,
)
from .readback import clause_to_formula, hypothesis_to_formulas
from .separation import SeparationReport, check_separation

__all__ = [
    "Example", "IlpTask", "IlpEncodingError", "task_from_structures",
    "to_prolog_atom",
    "clause_to_formula", "hypothesis_to_formulas",
    "SeparationReport", "check_separation",
]
