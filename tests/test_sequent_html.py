"""HTML rendering for sequent-calculus derivations
(``unicode_logic_kit.atp.sequent.Derivation.to_html``).

The oracle for content is DIFFERENTIAL against
:func:`~unicode_logic_kit.atp.sequent.render_sequent_proof` (the trusted text
renderer, hand-checked in ``test_sequent.py`` and ``docs/guide/
classical-reasoning.md``): every node's ``Γ ⊢ Δ`` string, rule name, and
``extra`` annotation that the text renderer prints must also appear (HTML-
escaped) in the HTML page. Tree *shape* is checked independently by rebuilding
a lightweight DOM from the generated markup and comparing each node's
``.pr``-child ``.nd`` count, recursively, against ``len(derivation.premises)``
— not derived from ``_html_sequent``'s own recursion, but from parsing its
output back and counting divs.
"""

import html.parser

from unicode_logic_kit.fol.nodes import (
    Atom, And, Or, Not, Quantifier, Variable, Constant,
)
from unicode_logic_kit.atp.sequent import (
    Sequent, Derivation, sequent, derive, axiom,
    check_sequent_proof, render_sequent_proof,
)

P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])


def _esc(s: str) -> str:
    """The same escaping ``to_html`` applies (mirrors ``atp._html.esc_html``)."""
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _forall_l_proof() -> Derivation:
    """∀x P(x) ⊢ P(c) via ∀L instantiating x := c — the exact worked example in
    docs/guide/classical-reasoning.md's "Sequent calculus" section."""
    x, c = Variable("x"), Constant("c")

    def Px(t):
        return Atom("P", [t])

    d = derive(sequent([Quantifier("∀", x, Px(x))], [Px(c)]), "∀L",
               axiom(sequent([Px(c)], [Px(c)])),
               extra=[c])
    assert check_sequent_proof(d)
    return d


def _conjunction_comm_proof() -> Derivation:
    """P∧Q ⊢ Q∧P via ∧R branching into two ∧L-closed premises (hand-checked,
    the exact example in docs/guide/classical-reasoning.md)."""
    PandQ = And(P, Q)
    comm = derive(sequent([PandQ], [And(Q, P)]), "∧R",
              derive(sequent([PandQ], [Q]), "∧L", axiom(sequent([P, Q], [Q]))),
              derive(sequent([PandQ], [P]), "∧L", axiom(sequent([P, Q], [P]))))
    assert check_sequent_proof(comm)
    return comm


def _fake_ternary_fixture() -> Derivation:
    """A hand-built 3-premise node (no LK rule has arity 3 — this exists only to
    exercise the HTML renderer's n-ary layout; it is never checked)."""
    return derive(sequent([P], [P]), "TernaryRule",
                  axiom(sequent([P], [P])),
                  axiom(sequent([Q], [Q])),
                  axiom(sequent([R], [R])))


# ---------------------------------------------------------------------------
# Well-formedness helper (identical approach to test_fitch_html.py's).
# ---------------------------------------------------------------------------

class _TagBalanceChecker(html.parser.HTMLParser):
    _VOID = {"meta", "br", "hr", "img", "input", "link"}

    def __init__(self):
        super().__init__()
        self.stack = []

    def handle_starttag(self, tag, attrs):
        if tag not in self._VOID:
            self.stack.append(tag)

    def handle_endtag(self, tag):
        assert self.stack and self.stack[-1] == tag, (
            f"unbalanced </{tag}>; open stack was {self.stack}")
        self.stack.pop()


def _assert_balanced(html_text: str):
    parser = _TagBalanceChecker()
    parser.feed(html_text)
    parser.close()
    assert parser.stack == [], f"unclosed tags at end of document: {parser.stack}"


# ---------------------------------------------------------------------------
# Lightweight DOM rebuild: only tracks <div> nesting + its "class" attribute,
# which is all the structural checks below need. Fed the WHOLE page (the CSS
# inside <style> contains no angle brackets, so it cannot be mistaken for
# markup); <meta> has no closing tag and is simply never pushed.
# ---------------------------------------------------------------------------

class _DivNode:
    __slots__ = ("classes", "children")

    def __init__(self, classes):
        self.classes = classes
        self.children = []


class _DomBuilder(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.roots = []
        self._stack = [self.roots]

    def handle_starttag(self, tag, attrs):
        if tag != "div":
            return
        node = _DivNode(set(dict(attrs).get("class", "").split()))
        self._stack[-1].append(node)
        self._stack.append(node.children)

    def handle_endtag(self, tag):
        if tag != "div":
            return
        self._stack.pop()


def _find_first(nodes, cls):
    """DFS for the first div (at any depth) carrying ``cls``."""
    for n in nodes:
        if cls in n.classes:
            return n
        found = _find_first(n.children, cls)
        if found is not None:
            return found
    return None


def _nd_arity_tree(node: "_DivNode"):
    """The shape of a ``.nd`` div's ``.pr``-children, recursively — a nested
    tuple mirroring ``Derivation.premises``' shape (``()`` for a leaf)."""
    pr = next((c for c in node.children if c.classes == {"pr"}), None)
    if pr is None:
        return ()
    kids = [c for c in pr.children if "nd" in c.classes]
    return tuple(_nd_arity_tree(k) for k in kids)


def _derivation_arity_tree(d: "Derivation"):
    return tuple(_derivation_arity_tree(p) for p in d.premises)


def _html_arity_tree(html_text: str):
    builder = _DomBuilder()
    builder.feed(html_text)
    builder.close()
    root = _find_first(builder.roots, "nd")
    assert root is not None, "no .nd node found in the rendered page"
    return _nd_arity_tree(root)


# ---------------------------------------------------------------------------
# Well-formedness / theming
# ---------------------------------------------------------------------------

def test_to_html_is_selfcontained_and_themed():
    html_text = _conjunction_comm_proof().to_html()
    assert html_text.startswith("<!doctype html>")
    assert "<style>" in html_text and "</style>" in html_text
    assert "prefers-color-scheme:dark" in html_text
    assert "data-theme=dark" in html_text
    assert "http://" not in html_text and "https://" not in html_text
    _assert_balanced(html_text)


def test_to_html_default_and_custom_title():
    assert "<title>Sequent derivation</title>" in _conjunction_comm_proof().to_html()
    assert "<title>My deriv</title>" in _conjunction_comm_proof().to_html(title="My deriv")


# ---------------------------------------------------------------------------
# Content fidelity — differential against render_sequent_proof's text output
# ---------------------------------------------------------------------------

def _walk(d: "Derivation"):
    yield d
    for p in d.premises:
        yield from _walk(p)


def test_to_html_contains_every_sequent_and_rule_render_sequent_proof_prints():
    d = _forall_l_proof()
    html_text = d.to_html()
    assert "∀L" in render_sequent_proof(d)  # sanity: the text renderer names the rule
    for node in _walk(d):
        assert _esc(str(node.conclusion)) in html_text
        assert _esc(node.rule) in html_text
    # The instantiation term (extra=[c]) that render_sequent_proof puts in the
    # bracketed label also shows up in the HTML's small "extra" annotation.
    assert _esc(Constant("c").to_unicode_str()) in html_text


def test_to_html_two_premise_rule_shows_both_branch_sequents():
    d = _conjunction_comm_proof()
    html_text = d.to_html()
    for node in _walk(d):
        assert _esc(str(node.conclusion)) in html_text


# ---------------------------------------------------------------------------
# Escaping
# ---------------------------------------------------------------------------

def test_to_html_escapes_markup_in_predicate_names():
    weird = Atom("A<b>&c", [])
    d = derive(sequent([weird], [weird]), "Reit-ish", axiom(sequent([weird], [weird])))
    html_text = d.to_html()
    assert "A&lt;b&gt;&amp;c" in html_text
    assert "A<b>&c" not in html_text
    _assert_balanced(html_text)


# ---------------------------------------------------------------------------
# Structural: n-ary premise arity in the HTML matches the derivation tree,
# recursively — rebuilt from the actual markup, not from the renderer's loop.
# ---------------------------------------------------------------------------

def test_to_html_arity_matches_derivation_tree_binary():
    d = _conjunction_comm_proof()
    # ∧R has two ∧L premises, each itself closed by one Ax leaf:
    #        P∧Q ⊢ Q∧P            [∧R]
    #   P∧Q⊢Q [∧L]      P∧Q⊢P [∧L]
    #   P,Q⊢Q [Ax]       P,Q⊢P [Ax]
    assert _derivation_arity_tree(d) == (((),), ((),))
    assert _html_arity_tree(d.to_html()) == _derivation_arity_tree(d)


def test_to_html_arity_matches_derivation_tree_unary_leaf():
    d = _forall_l_proof()
    assert _derivation_arity_tree(d) == ((),)              # ∀L: one Ax leaf
    assert _html_arity_tree(d.to_html()) == _derivation_arity_tree(d)


def test_to_html_arity_matches_derivation_tree_ternary_fixture():
    d = _fake_ternary_fixture()
    assert _derivation_arity_tree(d) == ((), (), ())        # 3 leaves
    assert _html_arity_tree(d.to_html()) == _derivation_arity_tree(d)
