"""Tests for the unicode_fol_kit command-line interface."""

import json
import sys

from unicode_fol_kit.__main__ import main


def test_tptp_output(capsys):
    """--to tptp renders the implication arrow as '=>'."""
    rc = main(["∀x (P(x) → Q(x))", "--to", "tptp"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "=>" in out


def test_latex_output(capsys):
    """--to latex emits the LaTeX \\forall command."""
    rc = main(["∀x P(x)", "--to", "latex"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "\\forall" in out


def test_msfl_strong_conjunction_unicode(capsys):
    """--mode msfl with a strong-conjunction formula renders '⊗' in unicode."""
    rc = main(["P(x) ⊗ Q(x)", "--mode", "msfl", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "⊗" in out


def test_invalid_formula_returns_1(capsys):
    """A syntactically invalid formula returns 1 and writes to stderr."""
    rc = main(["∀x (P(x)"])  # unbalanced parenthesis -> ParsingError
    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err.strip() != ""


def test_default_mode_and_format_is_tree(capsys):
    """With no flags the default rendering is the ASCII tree."""
    rc = main(["P(x)"])
    assert rc == 0
    out = capsys.readouterr().out
    # tree_str of an atom starts with the 'Atom:' label.
    assert "Atom: P" in out


def test_unicode_round_trip(capsys):
    """--to unicode reproduces the parsed formula."""
    rc = main(["∀x (P(x) → Q(x))", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "∀x (P(x) → Q(x))"


def test_json_output_is_valid_json(capsys):
    """--to json prints the versioned envelope with the node tree under 'root'."""
    rc = main(["P(x)", "--to", "json"])
    assert rc == 0
    out = capsys.readouterr().out
    data = json.loads(out)
    assert data["schema_version"] == 1
    assert data["root"]["_type"] == "Atom"


def test_prover9_output(capsys):
    """--to prover9 renders the implication as Prover9's '->'."""
    rc = main(["P(x) → Q(x)", "--to", "prover9"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "->" in out


def test_dot_output(capsys):
    """--to dot emits a Graphviz digraph header."""
    rc = main(["P(x)", "--to", "dot"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "digraph" in out


def test_invalid_character_returns_1(capsys):
    """A lexer-level failure (stray character) also returns 1."""
    rc = main(["P(x) @ Q(x)"])
    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err.strip() != ""


def test_msfol_sorted_quantifier_round_trip(capsys):
    """--mode msfol parses sort annotations and round-trips them in unicode."""
    rc = main(["∀x:Nat P(x)", "--mode", "msfol", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "∀x:Nat P(x)"


def test_fl_strong_disjunction_unicode(capsys):
    """--mode fl (unsorted Łukasiewicz) renders strong disjunction '⊕'."""
    rc = main(["P(x) ⊕ Q(x)", "--mode", "fl", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "⊕" in out


def test_circle_plus_is_xor_in_fol_but_strong_disjunction_in_fl(capsys):
    """The '⊕' glyph is mode-dependent: Xor in fol, StrongDisjunction in fl.

    The CLI must defer this to the parser mode rather than fixing one meaning.
    """
    rc = main(["P(x) ⊕ Q(x)", "--mode", "fol", "--to", "json"])
    assert rc == 0
    fol_data = json.loads(capsys.readouterr().out)
    assert fol_data["root"]["_type"] == "Xor"

    rc = main(["P(x) ⊕ Q(x)", "--mode", "fl", "--to", "json"])
    assert rc == 0
    fl_data = json.loads(capsys.readouterr().out)
    assert fl_data["root"]["_type"] == "StrongDisjunction"


def test_default_argv_reads_sys_argv(capsys, monkeypatch):
    """main() with no argument falls back to sys.argv[1:]."""
    monkeypatch.setattr(sys, "argv", ["unicode_fol_kit", "P(x)", "--to", "json"])
    rc = main()
    assert rc == 0
    data = json.loads(capsys.readouterr().out)
    assert data["root"]["_type"] == "Atom"


def test_msfol_mode_rejects_strong_conjunction(capsys):
    """⊗ is not a classical operator: msfol mode must reject it (returns 1)."""
    rc = main(["P(x) ⊗ Q(x)", "--mode", "msfol"])
    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err.strip() != ""


# ---------------------------------------------------------------------------
# New --mode choices: modal, second_order, dependence, linear, lambek.
# ---------------------------------------------------------------------------

def test_modal_mode_parses_box(capsys):
    """--mode modal parses the modal operator □ and round-trips it in unicode."""
    rc = main(["□P → ◇Q", "--mode", "modal", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "□P → ◇Q"


def test_second_order_mode_parses_predicate_quantifier(capsys):
    """--mode second_order parses ∀P (a second-order predicate quantifier)."""
    rc = main(["∀P P(x)", "--mode", "second_order", "--to", "json"])
    assert rc == 0
    data = json.loads(capsys.readouterr().out)
    assert data["root"]["_type"] == "SecondOrderQuantifier"


def test_dependence_mode_parses_dependence_atom(capsys):
    """--mode dependence parses the =(...) dependence atom."""
    rc = main(["=(x, y)", "--mode", "dependence", "--to", "json"])
    assert rc == 0
    data = json.loads(capsys.readouterr().out)
    assert data["root"]["_type"] == "Dependence"


def test_linear_mode_parses_tensor(capsys):
    """--mode linear parses ⊗ as the linear-logic Tensor, and round-trips it."""
    rc = main(["A ⊗ B", "--mode", "linear", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "A ⊗ B"


def test_lambek_mode_parses_product(capsys):
    """--mode lambek parses • as the Lambek product, and round-trips it."""
    rc = main(["A • B", "--mode", "lambek", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "A • B"


def test_modal_mode_latex_output(capsys):
    """--mode modal --to latex renders the □ operator as \\Box."""
    rc = main(["□P", "--mode", "modal", "--to", "latex"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "\\Box" in out


# ---------------------------------------------------------------------------
# Subcommands: check / equiv / prove / countermodel / repair / translate.
#
# Dispatch is on argv[0]: main() routes to a subcommand parser iff argv[0] is
# one of {check, equiv, prove, countermodel, repair, translate}, else to the
# legacy single-formula parser above. Every subcommand mirrors one
# unicode_fol_kit.api verb 1:1; see unicode_fol_kit/__main__.py's module
# docstring for the shared --dialect/--json/--timeout flags and error culture
# (BackendUnavailable/ValueError/NotImplementedError/OSError -> clean stderr
# message + exit 3, never a traceback).
# ---------------------------------------------------------------------------

# -- check ---------------------------------------------------------------- #

def test_check_cmd_closed_formula_is_ok(capsys):
    """'∀x P(x)' is closed, arity-consistent, lambda-free -> ok=True, exit 0."""
    rc = main(["check", "∀x P(x)"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "ok: True" in out
    assert "is_closed: True" in out


def test_check_cmd_free_variable_json(capsys):
    """'P(x)' has 'x' free (no binder) -> ok=False, exit 1; --json exposes it."""
    rc = main(["check", "P(x)", "--json"])
    assert rc == 1
    data = json.loads(capsys.readouterr().out)
    assert data["ok"] is False
    assert data["is_closed"] is False
    assert data["free_variables"] == ["x"]


def test_check_cmd_signature_violation(capsys, tmp_path):
    """A predicate absent from the --signature file is flagged unknown_predicate.

    The signature only lists P/1; 'Q' in '∀x Q(x)' is closed and well-formed
    on its own but not in the signature, so ok=False and the CLI must exit 1.
    """
    sig_path = tmp_path / "sig.json"
    sig_path.write_text(json.dumps({"predicates": {"P": 1}}), encoding="utf-8")
    rc = main(["check", "∀x Q(x)", "--signature", str(sig_path), "--json"])
    assert rc == 1
    data = json.loads(capsys.readouterr().out)
    assert data["ok"] is False
    assert data["signature_errors"][0]["kind"] == "unknown_predicate"
    assert data["signature_errors"][0]["symbol"] == "Q"


def test_check_cmd_signature_conformant_is_ok(capsys, tmp_path):
    """The same signature accepts '∀x P(x)' (P/1 is listed) -> exit 0."""
    sig_path = tmp_path / "sig.json"
    sig_path.write_text(json.dumps({"predicates": {"P": 1}}), encoding="utf-8")
    rc = main(["check", "∀x P(x)", "--signature", str(sig_path)])
    assert rc == 0


# -- equiv ------------------------------------------------------------------ #

def test_equiv_cmd_true_exit0(capsys):
    """'P → Q' and '¬P ∨ Q' are the textbook material-implication identity —
    Z3 proves ¬((P→Q) ↔ (¬P∨Q)) unsat -> equivalent=True, exit 0."""
    rc = main(["equiv", "P → Q", "¬P ∨ Q"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "equivalent: True" in out


def test_equiv_cmd_false_exit1_json(capsys):
    """'P' and 'Q' are independent atoms: P=True,Q=False refutes their
    equivalence -> equivalent=False (with a Z3 witness), exit 1."""
    rc = main(["equiv", "P", "Q", "--json"])
    assert rc == 1
    data = json.loads(capsys.readouterr().out)
    assert data["equivalent"] is False
    assert data["counterexample"]["kind"] == "z3_model"


def test_equiv_cmd_unknown_exit2(capsys):
    """A quantified modal Iff routes past the propositional modal tableau
    (which only decides quantifier-free formulas) to qml_equivalent, whose
    contract is sound-but-incomplete: it can only ever return True or None,
    never a refutation -- so an inequivalent pair like '∀x □P(x)' and 'Q'
    comes back equivalent=None (unknown), exit 2."""
    rc = main(["equiv", "∀x □P(x)", "Q", "--dialect", "modal"])
    assert rc == 2
    out = capsys.readouterr().out
    assert "equivalent: None" in out


# -- prove -------------------------------------------------------------- #

def test_prove_cmd_modus_ponens_proved_exit0(capsys):
    """Premises P, P → Q entail Q (modus ponens) -- Z3 (first in the default
    fol chain) closes it immediately -> status=proved, exit 0."""
    rc = main(["prove", "Q", "--premise", "P", "--premise", "P → Q"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "status: proved" in out
    assert "backend: z3" in out


def test_prove_cmd_forall_refuted_exit1_json(capsys):
    """'∀x P(x)' with no premises asks whether it is VALID (true in every
    model). It is not: the one-element domain with P false refutes it, so
    Z3 finds a countermodel -> status=refuted, exit 1."""
    rc = main(["prove", "∀x P(x)", "--json"])
    assert rc == 1
    data = json.loads(capsys.readouterr().out)
    assert data["status"] == "refuted"
    assert data["backend"] == "z3"
    assert data["logic"] == "fol"
    assert "wall_time" in data and "szs_status" in data


def test_prove_cmd_temporal_invalid_refuted_exit1(capsys):
    """'Ⓕ P → P' (Eventually P implies P) is genuinely INVALID (Eventually is
    read over the reflexive-transitive closure, so P can hold at a later
    world while failing at the current one). Since the kripke-enum backend
    joined the default modal chain this is REFUTED with a two-world witness
    (modal-tableau still bails UNKNOWN/unsupported first — no temporal rule);
    before that wave the whole chain came back unknown/exit 2."""
    rc = main(["prove", "Ⓕ P → P", "--dialect", "modal"])
    assert rc == 1
    out = capsys.readouterr().out
    assert "status: refuted" in out
    assert "backend: kripke-enum" in out


def test_prove_cmd_unknown_backend_name_exit3(capsys):
    """An unregistered backend name is a caller error (get_backend raises
    ValueError) -> clean stderr message, exit 3, no traceback."""
    rc = main(["prove", "P", "--backends", "bogus_backend"])
    assert rc == 3
    captured = capsys.readouterr()
    assert captured.err.strip() != ""
    assert "bogus_backend" in captured.err


def test_prove_cmd_explicit_backends_list(capsys):
    """--backends threads a custom single-backend chain through to api.prove."""
    rc = main(["prove", "Q", "--premise", "P", "--premise", "P → Q",
              "--backends", "z3"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "backend: z3" in out


# -- countermodel ----------------------------------------------------------- #

def test_countermodel_cmd_found_exit0(capsys):
    """'∀x P(x)' has a one-element countermodel (P false there) -> found, exit 0."""
    rc = main(["countermodel", "∀x P(x)"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "found: True" in out


def test_countermodel_cmd_not_found_exit1_json(capsys):
    """'P(x) ∨ ¬P(x)' is a tautology (excluded middle) -- no countermodel
    exists, so every backend in the chain reports nothing -> found=False,
    exit 1."""
    rc = main(["countermodel", "P(x) ∨ ¬P(x)", "--json"])
    assert rc == 1
    data = json.loads(capsys.readouterr().out)
    assert data["found"] is False
    assert data["model"] is None


# -- repair ------------------------------------------------------------- #

def test_repair_cmd_already_ok_exit0(capsys):
    """A closed, well-formed formula converges on the first (only) round."""
    rc = main(["repair", "∀x (P(x) → P(x))"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "ok: True" in out
    assert "converged: True" in out


def test_repair_cmd_free_variable_suggests_binding_exit1(capsys):
    """'P(x)' has a free variable -- the diagnosis names it and suggests
    quantifying or renaming it (api.repair's _suggest, is_closed branch)."""
    rc = main(["repair", "P(x)"])
    assert rc == 1
    out = capsys.readouterr().out
    assert "ok: False" in out
    assert "free variable" in out
    assert "x" in out


def test_repair_cmd_syntax_error_json(capsys):
    """An unbalanced parenthesis fails every dialect in the ladder -- the
    diagnosis is a syntax fix suggestion, not a CheckResult (parse never
    succeeded)."""
    rc = main(["repair", "∀x (P(x)", "--json"])
    assert rc == 1
    data = json.loads(capsys.readouterr().out)
    assert data["ok"] is False
    assert data["diagnostics"]["check"] is None
    assert data["diagnostics"]["parse"] is not None
    assert "Fix the syntax" in data["suggestion"]


# -- translate -------------------------------------------------------------- #

def test_translate_cmd_modal_to_fol(capsys):
    """□P under the standard translation becomes '∀w' (universally quantify
    every R-successor of the free anchor world w) 'R(w,w0) → P(w0)' -- the
    textbook modal-to-FOL encoding (comorphism.py's 'standard_translation' edge)."""
    rc = main(["translate", "□P", "--from", "modal", "--to-logic", "fol"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "path: standard_translation" in out
    assert "R(w, w0)" in out
    assert "P(w0)" in out


def test_translate_cmd_alc_to_fol_json(capsys):
    """∃r.C (an ALC concept: 'has an r-successor in C') translates to the FOL
    formula ∃x_1 (r(x,x_1) ∧ C(x_1)) with x the free anchor individual
    (comorphism.py's 'concept_to_fol' edge, dl/translate.py's convention)."""
    rc = main(["translate", "∃r.C", "--from", "alc", "--to-logic", "fol", "--json"])
    assert rc == 0
    data = json.loads(capsys.readouterr().out)
    assert data["source"] == "alc"
    assert data["target"] == "fol"
    assert data["path"] == ["concept_to_fol"]
    assert data["lossy"] is False


def test_translate_cmd_unknown_logic_label_exit3(capsys):
    """A logic label absent from the comorphism registry has no BFS path --
    ComorphismRegistry.find_path raises ValueError, caught cleanly -> exit 3."""
    rc = main(["translate", "P", "--from", "bogus", "--to-logic", "fol"])
    assert rc == 3
    captured = capsys.readouterr()
    assert captured.err.strip() != ""
    assert "bogus" in captured.err


def test_translate_cmd_unparseable_formula_exit3(capsys):
    """A formula the chosen dialect cannot parse is a caller error before
    translate() is even reached -> exit 3, not a traceback."""
    rc = main(["translate", "∀x (P(x)", "--from", "fol", "--to-logic", "modal"])
    assert rc == 3
    captured = capsys.readouterr()
    assert captured.err.strip() != ""


# -- legacy regression: the new subcommand dispatch must not disturb it ---- #

def test_legacy_regression_after_subcommand_dispatch_added(capsys):
    """A plain formula (argv[0] not in the subcommand set) still goes through
    the untouched legacy single-formula path -- --mode/--to combined, exactly
    as before subcommands existed."""
    rc = main(["∀x (P(x) → Q(x))", "--mode", "fol", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "∀x (P(x) → Q(x))"
