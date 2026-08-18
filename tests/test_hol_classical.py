"""Structural + faithfulness tests for the classical FOL/MSFOL → THF/Isabelle exporters."""

import pytest

from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant, Box,
)
from unicode_fol_kit.hol.classical import (
    to_thf_fol, to_isabelle_fol, to_thf_msfol, to_isabelle_msfol,
)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _balanced(s: str) -> bool:
    depth = 0
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


X = Variable("x")
Y = Variable("y")


# ---------------------------------------------------------------------------
# THF: structural well-formedness
# ---------------------------------------------------------------------------

def test_thf_fol_basic_structure():
    f = Quantifier("∀", X, Implies(Atom("Human", [X]), Atom("Mortal", [X])))
    out = to_thf_fol(f)
    # A conjecture line and one declaration per predicate.
    assert "thf(goal, conjecture," in out
    assert "thf(human_decl, type, ( human : ( $i > $o ) ))." in out
    assert "thf(mortal_decl, type, ( mortal : ( $i > $o ) ))." in out
    # Universal binder and the THF implication operator are present, applicative form.
    assert "! [X: $i]" in out
    assert "( human @ X ) => ( mortal @ X )" in out
    assert _balanced(out)


def test_thf_every_symbol_declared():
    # predicate P/2, function f/1, constant a, number 7 must each get a type decl.
    f = Atom("P", [Function("f", [Constant("a")]), Number(7)])
    out = to_thf_fol(f)
    for needle in [
        "( p : ( $i > $i > $o ) )",   # predicate P, arity 2
        "( f : ( $i > $i ) )",        # function f, arity 1
        "( a : $i )",                 # constant a
        "( n7 : $i )",                # number 7 -> n7
    ]:
        assert needle in out, needle
    assert "( p @ ( f @ a ) @ n7 )" in out
    assert _balanced(out)


def test_thf_equality_is_uninterpreted():
    f = Atom("=", [Constant("a"), Constant("b")])
    out = to_thf_fol(f)
    # '=' must NOT be primitive HOL identity; it is the uninterpreted predicate feq.
    assert "( feq : ( $i > $i > $o ) )" in out
    assert "( feq @ a @ b )" in out
    assert " = " not in out.split("conjecture,")[1]  # no primitive = in the goal body


def test_thf_connectives_mapping():
    f = Iff(Or(Atom("A", []), Not(Atom("B", []))), Xor(Atom("A", []), Atom("B", [])))
    out = to_thf_fol(f)
    body = out.split("conjecture,")[1]
    assert "<=>" in body          # Iff
    assert "|" in body            # Or
    assert "~ " in body           # Not
    assert "<~>" in body          # Xor
    # nullary predicates are bare functors, declared with result type $o.
    assert "( a : ( $o ) )" in out
    assert "( b : ( $o ) )" in out


def test_thf_free_variables_are_closed():
    f = Atom("P", [X, Y])
    out = to_thf_fol(f)
    # free x, y get universally closed (TPTP rejects free vars in a role formula).
    body = out.split("conjecture,")[1]
    assert "! [X: $i]" in body
    assert "! [Y: $i]" in body


def test_thf_axiom_role():
    f = Atom("A", [])
    out = to_thf_fol(f, conjecture=False)
    assert "thf(goal, axiom," in out
    assert "conjecture" not in out.split("\n")[-2]


def test_thf_rejects_modal():
    f = Box(Atom("A", []))
    with pytest.raises(NotImplementedError):
        to_thf_fol(f)


# ---------------------------------------------------------------------------
# THF: MSFOL guard relativization
# ---------------------------------------------------------------------------

def test_thf_msfol_sorted_quantifier_relativized():
    # ∀x:Human Mortal(x)  ==>  ∀x. Human(x) => Mortal(x)
    f = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X]))
    out = to_thf_msfol(f)
    body = out.split("conjecture,")[1]
    assert "! [X: $i]" in body
    assert "( human @ X ) => ( mortal @ X )" in body
    # the sort became an ordinary unary guard predicate.
    assert "( human : ( $i > $o ) )" in out


def test_thf_msfol_existential_relativized():
    # ∃x:Human Mortal(x)  ==>  ∃x. Human(x) & Mortal(x)
    f = SortedQuantifier("∃", X, "Human", Atom("Mortal", [X]))
    body = to_thf_msfol(f).split("conjecture,")[1]
    assert "? [X: $i]" in body
    assert "( human @ X ) & ( mortal @ X )" in body


def test_thf_msfol_sort_facts_for_constant():
    f = Atom("Mortal", [SortedConstant("socrates", "Human")])
    out = to_thf_msfol(f, include_sort_facts=True)
    body = out.split("conjecture,")[1]
    # the sort-membership fact Human(socrates) is conjoined.
    assert "( human @ socrates )" in body
    assert "( mortal @ socrates )" in body
    assert "&" in body


# ---------------------------------------------------------------------------
# Isabelle: structural well-formedness
# ---------------------------------------------------------------------------

def test_isabelle_fol_is_real_lemma():
    f = Quantifier("∀", X, Implies(Atom("Human", [X]), Atom("Mortal", [X])))
    out = to_isabelle_fol(f)
    assert out.startswith("theory FOL_Export")
    assert "imports Main" in out
    assert out.rstrip().endswith("end")
    # a genuine lemma (not commented out) over uninterpreted consts.
    assert "lemma goal: " in out
    assert "consts human :: \"i \\<Rightarrow> bool\"" in out
    assert "consts mortal :: \"i \\<Rightarrow> bool\"" in out
    assert "typedecl i" in out
    # the lemma body uses HOL quantifiers and connectives.
    assert "\\<forall> x." in out
    assert "\\<longrightarrow>" in out
    # the lemma is stated, left open with 'oops' by default (loads without claiming proof).
    assert "\n  oops\n" in out


def test_isabelle_lemma_not_in_comment():
    # The reference broken skeleton put the lemma inside a (* ... *) comment.
    # Ours must emit a real top-level lemma keyword OUTSIDE any comment.
    f = Atom("P", [Constant("a")])
    out = to_isabelle_fol(f)
    # find the lemma line and ensure it is not within a comment block.
    lines = out.splitlines()
    lemma_lines = [l for l in lines if l.startswith("lemma ")]
    assert len(lemma_lines) == 1
    assert "(*" not in lemma_lines[0]


def test_isabelle_custom_proof_tactic():
    f = Or(Atom("A", []), Not(Atom("A", [])))
    out = to_isabelle_fol(f, proof="by auto")
    assert "\n  by auto\n" in out
    assert "oops" not in out


def test_isabelle_function_and_constant_consts():
    f = Atom("P", [Function("f", [Constant("a")])])
    out = to_isabelle_fol(f)
    assert "consts f :: \"i \\<Rightarrow> i\"" in out
    assert "consts a :: \"i\"" in out
    assert "consts p :: \"i \\<Rightarrow> bool\"" in out
    # curried application in the lemma body.
    assert "(p (f a))" in out


def test_isabelle_equality_uninterpreted():
    f = Atom("=", [Constant("a"), Constant("b")])
    out = to_isabelle_fol(f)
    assert "consts feq :: \"i \\<Rightarrow> i \\<Rightarrow> bool\"" in out
    assert "(feq a b)" in out


def test_isabelle_xor_is_negated_iff():
    f = Xor(Atom("A", []), Atom("B", []))
    out = to_isabelle_fol(f)
    assert "\\<not> ((a \\<longleftrightarrow> b))" in out or \
           "\\<not> (a \\<longleftrightarrow> b)" in out


def test_isabelle_msfol_relativized():
    f = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X]))
    out = to_isabelle_msfol(f)
    assert "consts human :: \"i \\<Rightarrow> bool\"" in out
    assert "\\<forall> x." in out
    assert "(human x) \\<longrightarrow> (mortal x)" in out


def test_isabelle_rejects_modal():
    with pytest.raises(NotImplementedError):
        to_isabelle_fol(Box(Atom("A", [])))


# ---------------------------------------------------------------------------
# faithfulness: every signature symbol used in the body is declared, and the
# THF body re-tokenizes to the same operator/atom skeleton as the source AST.
# ---------------------------------------------------------------------------

def test_thf_declares_exactly_the_used_predicates():
    f = And(Atom("P", [X]), Atom("Q", [X, Constant("c")]))
    out = to_thf_fol(f)
    # both predicates + the constant are declared; nothing spurious.
    assert out.count("type,") == 3  # p, q, c
    assert "( p : ( $i > $o ) )" in out
    assert "( q : ( $i > $i > $o ) )" in out
    assert "( c : $i )" in out


def test_thf_quantifier_count_matches_source():
    # two nested quantifiers in source -> two binders in the THF body.
    f = Quantifier("∀", X, Quantifier("∃", Y, Atom("R", [X, Y])))
    body = to_thf_fol(f).split("conjecture,")[1]
    assert body.count("! [X: $i]") == 1
    assert body.count("? [Y: $i]") == 1


def test_msfol_matches_to_fol_then_to_thf():
    # to_thf_msfol(f) must equal to_thf_fol(to_fol(f)) — the documented contract.
    from unicode_fol_kit.fol.nodes import to_fol
    f = SortedQuantifier("∀", X, "Animal",
                         Implies(Atom("Dog", [X]), Atom("Mammal", [X])))
    assert to_thf_msfol(f, include_sort_facts=True) == \
        to_thf_fol(to_fol(f, include_sort_facts=True))


# ---------------------------------------------------------------------------
# REGRESSION: distinct source symbols must map to distinct emitted identifiers.
# (See module: the global _SymbolResolver keyed by (category, raw_name, arity).)
# ---------------------------------------------------------------------------

from unicode_fol_kit.atp.z3_models import is_valid  # noqa: E402


def _bodies(out):
    """(thf/isa) split helper: the goal/lemma body of a THF emission."""
    return out.split("conjecture,")[1]


def test_safe_name_collision_does_not_fake_a_tautology_thf():
    # HOLE (1) SOUNDNESS: 'Ab' and 'ab' both sanitised to 'ab', so
    # Implies(Ab, ab) (NOT valid) emitted as the tautology '( ab => ab )'.
    f = Implies(Atom("Ab", []), Atom("ab", []))
    # ground truth: the implication of two DISTINCT atoms is not valid.
    assert is_valid(f) is False
    out = to_thf_fol(f)
    body = _bodies(out)
    # The two atoms must stay DISTINCT in the emitted body (no '( ab => ab )').
    import re
    m = re.search(r"\(\s*(\w+)\s*=>\s*(\w+)\s*\)", body)
    assert m is not None, body
    lhs, rhs = m.group(1), m.group(2)
    assert lhs != rhs, f"collapsed to a tautology: {body!r}"
    # exactly two distinct nullary-predicate declarations.
    assert out.count("type,") == 2
    # and the goal is provably not a syntactic tautology of the form (q => q).
    assert "( ab => ab )" not in body


def test_safe_name_collision_does_not_fake_a_tautology_isabelle():
    f = Implies(Atom("Ab", []), Atom("ab", []))
    assert is_valid(f) is False
    out = to_isabelle_fol(f)
    import re
    m = re.search(r"\((\w+) \\<longrightarrow> (\w+)\)", out)
    assert m is not None, out
    assert m.group(1) != m.group(2), out
    # two distinct consts declarations, no duplicate 'consts' name.
    consts = [l for l in out.splitlines() if l.startswith("consts ")]
    names = [l.split()[1] for l in consts]
    assert len(names) == len(set(names)) == 2, consts


def test_cross_category_name_emits_distinct_decls_thf():
    # HOLE (2): 'p' used as a nullary predicate AND as a constant must yield TWO
    # decls with distinct identifiers and their proper (conflicting) types.
    f = And(Atom("p", []), Atom("Q", [Constant("p")]))
    out = to_thf_fol(f)
    # one decl is the nullary predicate p:$o, the other the constant p':$i.
    decls = [l for l in out.splitlines() if l.startswith("thf(")]
    idents = [l.split(",")[0][len("thf("):] for l in decls if "type" in l]
    # strip the trailing '_decl'
    bare = [i[:-len("_decl")] for i in idents]
    assert len(bare) == len(set(bare)), decls  # all decl names distinct
    # both an $o (predicate) and an $i (constant) decl exist, on different names.
    o_decls = [l for l in decls if ": ( $o )" in l]
    i_decls = [l for l in decls if l.rstrip().endswith(": $i )).")]
    assert len(o_decls) == 1 and len(i_decls) == 1
    assert o_decls[0].split(",")[0] != i_decls[0].split(",")[0]


def test_cross_category_name_no_duplicate_consts_isabelle():
    # HOLE (2): loadability — no two 'consts' with the same name / conflicting types.
    f = And(Atom("p", []), Atom("Q", [Constant("p")]))
    out = to_isabelle_fol(f)
    consts = [l for l in out.splitlines() if l.startswith("consts ")]
    names = [l.split()[1] for l in consts]
    assert len(names) == len(set(names)), consts
    # exactly one bool (nullary pred) and one i (constant) for the 'p' family.
    assert any(l.endswith('"bool"') for l in consts)
    assert any(l.endswith('"i"') for l in consts)


def test_user_feq_does_not_collide_with_equality_alias():
    # HOLE (2): a user predicate literally named 'feq' must not collide with the
    # '=' alias target 'feq'.
    f = And(Atom("feq", [Constant("a")]), Atom("=", [Constant("a"), Constant("b")]))
    out = to_thf_fol(f)
    decls = [l for l in out.splitlines() if l.startswith("thf(") and "type" in l]
    # the unary user feq and the binary '=' alias must be DISTINCT symbols/types.
    unary = [l for l in decls if ": ( $i > $o )" in l]
    binary = [l for l in decls if ": ( $i > $i > $o )" in l]
    assert len(unary) == 1 and len(binary) == 1
    assert unary[0].split(",")[0] != binary[0].split(",")[0], decls


def test_predicate_at_two_arities_is_two_distinct_symbols_thf():
    # HOLE (3) SOUNDNESS: P/1 and P/2 must be TWO distinct, well-typed symbols,
    # not one symbol applied at two arities.
    f = And(Atom("P", [X]), Atom("P", [X, Y]))
    out = to_thf_fol(f)
    body = _bodies(out)
    decls = [l for l in out.splitlines() if l.startswith("thf(") and "type" in l]
    unary = [l for l in decls if ": ( $i > $o )" in l]
    binary = [l for l in decls if ": ( $i > $i > $o )" in l]
    assert len(unary) == 1 and len(binary) == 1, decls
    u_name = unary[0].split(":")[0].split("(")[-1].strip()
    b_name = binary[0].split(":")[0].split("(")[-1].strip()
    assert u_name != b_name
    # the body must apply each at exactly its declared arity, with distinct heads.
    assert f"( {u_name} @ X )" in body
    assert f"( {b_name} @ X @ Y )" in body
    # the unary head is NOT applied to two args anywhere.
    assert f"( {u_name} @ X @ Y )" not in body


def test_predicate_at_two_arities_is_two_distinct_consts_isabelle():
    f = And(Atom("P", [X]), Atom("P", [X, Y]))
    out = to_isabelle_fol(f)
    consts = [l for l in out.splitlines() if l.startswith("consts ")]
    names = [l.split()[1] for l in consts]
    assert len(names) == len(set(names)) == 2, consts
    # one i⇒bool and one i⇒i⇒bool, distinct names.
    assert any(l.endswith('"i \\<Rightarrow> bool"') for l in consts)
    assert any(l.endswith('"i \\<Rightarrow> i \\<Rightarrow> bool"') for l in consts)


def test_every_used_head_is_declared_after_decollision():
    # Faithfulness across all three holes at once: every functor token that
    # appears applied in the THF body has a matching declaration (closed world).
    f = And(
        Implies(Atom("Ab", []), Atom("ab", [])),
        And(Atom("P", [Constant("p")]), Atom("P", [Constant("p"), Constant("p")])),
    )
    out = to_thf_fol(f)
    decl_names = set()
    for l in out.splitlines():
        if l.startswith("thf(") and "type" in l:
            decl_names.add(l.split(",")[0][len("thf("):][:-len("_decl")])
    # collect every head identifier used in the body (token before ' @' or bare atoms)
    body = _bodies(out)
    import re
    used = set(re.findall(r"\b([a-z]\w*)\b", body))
    used.discard("i")  # type token noise is absent from $-prefixed types anyway
    # every emitted decl name is unique...
    assert len(decl_names) == len(set(decl_names))
    # ...and every used lowercase identifier is among the declared ones.
    assert used <= decl_names, used - decl_names


# ---------------------------------------------------------------------------
# `_SymbolResolver`/`_sanitize` legalise (de-collide, escape punctuation,
# prefix a digit lead) AND transliterate to ASCII via `constant_name_to_ascii`
# (Greek -> conventional name, everything else non-ASCII -> a reversible
# `uXXXX` codepoint escape), so a name with non-ASCII letters no longer reaches
# the emitted THF/Isabelle text at all — only its transliteration does.
#
# HISTORY / WHY THIS CLASS CHANGED (not just got new tests): this class used to
# be named `TestNonAsciiNamesReachThfAndIsabelleVerbatim` and pinned the
# OPPOSITE, broken behaviour on purpose, as a documented bug report: THF and
# Isabelle are ASCII-only target formats (TPTP `lower_word`, Isabelle
# identifiers), and `str.isalnum()` is `True` for nearly every Unicode letter,
# so the old filter waved non-ASCII letters through as "harmless" -- silent
# corruption of the exported problem, not sanitisation. Per the task's (R4),
# updating a test that pins TODAY's output is only correct when that output
# was illegal in the target format to begin with; that is exactly this case
# (a raw `ś`/`中` in an unquoted TPTP/Isabelle identifier is not legal there),
# so the old assertions are replaced with the fixed, ASCII-pure ones rather
# than kept. No assertion on an already-ASCII name changes anywhere in this
# file — see `TestAsciiNamesUnaffectedByAsciiTransliteration` below for that
# guarantee made explicit.
# ---------------------------------------------------------------------------

class TestNonAsciiNamesAreTransliteratedInThfAndIsabelle:
    def test_non_ascii_constant_in_thf(self):
        # 'świątek' -> constant_name_to_ascii -> 'u015bwiu0105tek' (ś=U+015B,
        # ą=U+0105 each escaped; plain ASCII letters pass through unchanged).
        f = Atom("P", [Constant("świątek")])
        out = to_thf_fol(f)
        assert "świątek" not in out
        assert "thf(u015bwiu0105tek_decl, type, ( u015bwiu0105tek : $i ))." in out
        assert "( p @ u015bwiu0105tek )" in out

    def test_non_ascii_constant_in_isabelle(self):
        f = Atom("P", [Constant("świątek")])
        out = to_isabelle_fol(f)
        assert "świątek" not in out
        assert 'consts u015bwiu0105tek :: "i"' in out
        assert '"(p u015bwiu0105tek)"' in out

    def test_non_ascii_predicate_in_thf(self):
        # 'Świątek' -> constant_name_to_ascii -> 'u015awiu0105tek' (Ś=U+015A,
        # a DIFFERENT escape than lower-case 'świątek' above -- the fix must
        # not accidentally collapse the two). _sanitize's first-letter fold
        # then has no effect (the transliterated stem already starts 'u').
        f = Atom("Świątek", [X])
        out = to_thf_fol(f)
        assert "Świątek" not in out and "świątek" not in out
        assert "thf(u015awiu0105tek_decl, type, ( u015awiu0105tek : ( $i > $o ) ))." in out

    def test_cjk_constant_in_thf_and_isabelle(self):
        # '中文' -> 'u4e2du6587' (U+4E2D, U+6587), ASCII-pure in both exports.
        f = Atom("P", [Constant("中文")])
        thf = to_thf_fol(f)
        isa = to_isabelle_fol(f)
        assert "中文" not in thf and "中文" not in isa
        assert "u4e2du6587" in thf
        assert "u4e2du6587" in isa

    def test_diacritic_lookalike_constants_stay_distinct_thf(self):
        # (R2/R4 collision testfall) 'świątek' and its ASCII lookalike
        # 'swiatek' must NOT collapse onto the same THF constant: the
        # uXXXX-escape transliteration already keeps them apart (unlike a
        # lossy accent-strip would), and _SymbolResolver's dedupe is the
        # second line of defence if it ever didn't.
        f = And(Atom("P", [Constant("świątek")]), Atom("Q", [Constant("swiatek")]))
        out = to_thf_fol(f)
        const_decls = [l for l in out.splitlines() if l.rstrip().endswith(": $i )).")]
        assert len(const_decls) == 2, out
        idents = {l.split(",")[0][len("thf("):][:-len("_decl")] for l in const_decls}
        assert idents == {"u015bwiu0105tek", "swiatek"}

    def test_diacritic_lookalike_constants_stay_distinct_isabelle(self):
        f = And(Atom("P", [Constant("świątek")]), Atom("Q", [Constant("swiatek")]))
        out = to_isabelle_fol(f)
        consts = [l for l in out.splitlines() if l.startswith("consts ") and l.endswith('"i"')]
        names = {l.split()[1] for l in consts}
        assert names == {"u015bwiu0105tek", "swiatek"}


# ---------------------------------------------------------------------------
# (R1) backward compatibility: a name already legal in THF/Isabelle must come
# out of `_sanitize` byte-identically to before this fix.
# `constant_name_to_ascii` is the identity on a string where every character
# is already ASCII (see its own docstring), so inserting it ahead of the
# pre-existing alnum/underscore filter cannot change the result for such a
# name -- executed here directly against the private `_sanitize` (imported
# explicitly for this one regression-proof test; every other test in this
# file goes through the public `to_thf_fol`/`to_isabelle_fol` surface, and
# the fact that ~30 of them, written before this fix and pinning literal
# ASCII output, still pass unmodified is itself the same guarantee at the
# integration level).
# ---------------------------------------------------------------------------

from unicode_fol_kit.hol.classical import _sanitize  # noqa: E402


class TestAsciiNamesUnaffectedByAsciiTransliteration:
    @pytest.mark.parametrize("raw,expected", [
        ("socrates", "socrates"),          # plain lower ASCII: untouched
        ("Human", "human"),                # first letter folded, as before
        ("dani_Shapiro", "dani_Shapiro"),  # underscore continuation: untouched
        ("family_History", "family_History"),
        ("2008SummerOlympics", "p2008SummerOlympics"),  # digit lead: 'p'-prefixed, as before
        ("HasBond", "hasBond"),
        ("=", "feq"),                      # alias path, bypasses transliteration entirely
    ])
    def test_sanitize_matches_pre_fix_output(self, raw, expected):
        assert _sanitize(raw) == expected
