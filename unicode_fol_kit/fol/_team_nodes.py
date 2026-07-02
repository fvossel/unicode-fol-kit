"""Dependence-logic / IF-logic node classes and the ``dependence`` parser mode.

Dependence logic (Väänänen 2007) and independence-friendly (IF) logic extend
first-order syntax with constructs whose meaning lives in TEAM SEMANTICS — a
formula is satisfied by a SET of assignments (a team), not a single one:

- the **dependence atom** ``=(t₁, …, tₙ)``: in the current team, the value of
  ``tₙ`` is functionally determined by the values of ``t₁ … tₙ₋₁``
  (``=(t)`` with one argument is the constancy atom: ``t`` has the same value
  under every assignment of the team);
- the **slashed existential** ``∃x/{y, …} φ`` (IF logic): a witness for ``x``
  is chosen UNIFORMLY IN — i.e. independently of — the listed variables.

The ``dependence`` mode (``MSFLParser(dependence=True)``) is classical unsorted
FOL syntax restricted to the team-friendly fragment: literals, ``∧``, ``∨``
(read as the SPLITTING disjunction), ``∀`` / ``∃``, plus the two constructs
above. ``→`` / ``↔`` are deliberately absent — they have no faithful team
semantics in this fragment. Evaluation lives in
``unicode_fol_kit.semantics.team`` (``team_satisfies`` / ``team_models``);
dependence logic captures existential second-order logic, so there is no
classical export: ``to_z3`` / ``to_prover9`` / ``to_tptp`` reject.
"""

from dataclasses import dataclass
from typing import Tuple

from ._fol_nodes import (
    Node, Z3Env, Variable, Not, And, Or, Quantifier,
    NODE_CLASSES, register_parser_op, _fold_binary,
)

# Shared rejection message: team-semantic constructs have no classical export.
_NO_TEAM_EXPORT = (
    "Dependence/IF constructs (=(…) dependence atoms, slashed quantifiers) have "
    "team semantics — a formula is satisfied by a SET of assignments — and are "
    "expressively second-order, so they have no classical first-order export. "
    "Evaluate with unicode_fol_kit.team_satisfies / team_models over a finite "
    "Structure."
)


@dataclass(frozen=True)
class Dependence(Node):
    """A dependence atom ``=(t₁, …, tₙ)``: ``tₙ`` is determined by ``t₁ … tₙ₋₁``.

    ``args`` is a non-empty tuple of terms; the LAST is the dependent one. A
    team X satisfies it iff any two assignments in X that agree on
    ``t₁ … tₙ₋₁`` also agree on ``tₙ``. With a single argument, ``=(t)`` is the
    CONSTANCY atom: ``t`` takes one fixed value across the whole team.
    """

    args: Tuple[Node, ...]

    def __post_init__(self):
        """Coerce the args to a tuple and require at least one term."""
        object.__setattr__(self, "args", tuple(self.args))
        if len(self.args) < 1:
            raise ValueError("Dependence: =(…) needs at least one term.")

    def _tree_parts(self):
        """Return the =(…) label and the term children."""
        return "=(…)", list(self.args)

    def to_dict(self):
        """Serialise to dict with the recursively serialised terms."""
        return {"_type": "Dependence", "args": [a.to_dict() for a in self.args]}

    @staticmethod
    def from_dict(d):
        """Deserialise a Dependence from a dict produced by to_dict."""
        return Dependence(tuple(Node.from_dict(a) for a in d["args"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: dependence atoms are team-semantic."""
        raise NotImplementedError(_NO_TEAM_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: dependence atoms are team-semantic."""
        raise NotImplementedError(_NO_TEAM_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: dependence atoms are team-semantic."""
        raise NotImplementedError(_NO_TEAM_EXPORT)


@dataclass(frozen=True)
class SlashedExists(Node):
    """An IF-logic slashed existential ``∃x/{y, …} φ``.

    Binds ``variable`` over ``formula``; the witness for ``x`` must be chosen
    UNIFORMLY IN the variables listed in ``slashed`` (a tuple of names bound by
    ENCLOSING quantifiers): two team assignments that agree on everything
    except the slashed variables receive the same witness. Only the
    existential is slashed (a slashed universal adds nothing in this
    fragment).
    """

    variable: Variable
    slashed: Tuple[str, ...]
    formula: Node

    def __post_init__(self):
        """Coerce the slashed list to a tuple of names and validate it."""
        names = tuple(v.name if isinstance(v, Variable) else str(v)
                      for v in self.slashed)
        object.__setattr__(self, "slashed", names)
        if len(names) < 1:
            raise ValueError("SlashedExists: the slash set must name at least "
                             "one variable (∃x/{y} …).")

    def _tree_parts(self):
        """Return the slashed-∃ label (with variable and slash set) and the matrix."""
        return f"∃{self.variable.name}/{{{', '.join(self.slashed)}}}", [self.formula]

    def to_dict(self):
        """Serialise to dict with the bound variable, slash set, and matrix."""
        return {"_type": "SlashedExists", "variable": self.variable.to_dict(),
                "slashed": list(self.slashed), "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a SlashedExists from a dict produced by to_dict."""
        return SlashedExists(Node.from_dict(d["variable"]), tuple(d["slashed"]),
                             Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: slashed quantifiers are team-semantic."""
        raise NotImplementedError(_NO_TEAM_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: slashed quantifiers are team-semantic."""
        raise NotImplementedError(_NO_TEAM_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: slashed quantifiers are team-semantic."""
        raise NotImplementedError(_NO_TEAM_EXPORT)


NODE_CLASSES.update({"Dependence": Dependence, "SlashedExists": SlashedExists})


# =========================
# Parser registration — the "dependence" mode
# =========================
#
# Classical unsorted FOL syntax restricted to the team-friendly fragment:
# ¬ (semantically honest on atoms only — the evaluator enforces that), the
# splitting ∨ and ∧ (same-level, no mixing), plain ∀/∃, the dependence atom
# =(…), and the slashed ∃x/{y,…}. Deliberately NO → / ↔ / ⊕.

register_parser_op(Not, "dependence", "prefix", "not_", '"¬" prefix',
                   lambda items: Not(items[0]))
register_parser_op(And, "dependence", "level2", "and_", '"∧"',
                   lambda items: _fold_binary(items, And), only_name="only_and")
register_parser_op(Or, "dependence", "level2", "or_", '"∨"',
                   lambda items: _fold_binary(items, Or), only_name="only_or")
register_parser_op(Quantifier, "dependence", "quantifier", "quantifier_",
                   "(FORALL | EXISTS) VARIABLE prefix",
                   lambda items: Quantifier(str(items[0]), items[1], items[2]))


def _dep_transform(items):
    """Build a Dependence atom from the parenthesised termlist of =(…)."""
    args = items[0] if items and isinstance(items[0], list) else list(items)
    return Dependence(tuple(args))


def _slashed_transform(items):
    """Build a SlashedExists from [EXISTS, Variable, slashed Variables…, body]."""
    variable = items[1]
    slashed = tuple(v.name for v in items[2:-1])
    return SlashedExists(variable, slashed, items[-1])


# The '=(' form cannot collide with the infix 'term = term' atom: infix equality
# requires a term BEFORE the '='.
register_parser_op(Dependence, "dependence", "prefix", "dep_",
                   '"=" "(" termlist ")"', _dep_transform)
register_parser_op(SlashedExists, "dependence", "quantifier", "slashed_",
                   'EXISTS VARIABLE "/" "{" VARIABLE ("," VARIABLE)* "}" prefix',
                   _slashed_transform)
