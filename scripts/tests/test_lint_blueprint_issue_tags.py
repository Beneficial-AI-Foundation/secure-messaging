"""Tests for scripts/lint-blueprint-issue-tags.py (standard library unittest only)."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load_lint():
    spec = importlib.util.spec_from_file_location("lint_blueprint_issue_tags", SCRIPTS / "lint-blueprint-issue-tags.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


lint = load_lint()
FOOTER = "{githubLabel}`github` {githubIssue 5}[]"


class LintTest(unittest.TestCase):
    def setUp(self):
        self.chapters = Path(tempfile.mkdtemp()) / "Chapters"
        self.chapters.mkdir()

    def chapter(self, text: str, name: str = "A.lean"):
        (self.chapters / name).write_text(textwrap.dedent(text).lstrip("\n"))

    def run_lint(self):
        return lint.lint(self.chapters)

    def node(self, opts: str, body: str = "Text.", kind: str = "definition"):
        self.chapter(f'::::{kind} "lbl" {opts}\n{body}\n::::\n')
        return self.run_lint()

    def assertErrors(self, diags, count, *substrings):
        msgs = [str(d) for d in diags]
        self.assertEqual(len(diags), count, msgs)
        for s in substrings:
            self.assertTrue(any(s in m for m in msgs), (s, msgs))

    # grammar
    def test_issue_tag_passes(self):
        self.assertEqual(self.node('(tags := "gh-109")'), [])

    def test_several_issue_tags_pass(self):
        self.assertEqual(self.node('(tags := "gh-1, gh-2")'), [])

    def test_unrelated_tags_pass(self):
        self.assertEqual(self.node('(tags := "gh-109, crypto, Draft")'), [])

    def test_no_tags_passes(self):
        self.assertEqual(self.node('(parent := "x")'), [])

    def test_malformed_issue_tags(self):
        for bad in ("gh-01", "gh-", "gh-x", "GH-109"):
            with self.subTest(bad=bad):
                self.assertErrors(self.node(f'(tags := "{bad}")'), 1, "is not a valid issue tag")

    def test_duplicate_tag_tokens(self):
        self.assertErrors(self.node('(tags := "gh-109, GH-109")'), 2, "duplicate tag", "is not a valid issue tag")

    def test_malformed_tags_option_is_reported(self):
        for bad in ("(tags := 'gh-1')", "(tags := gh-1)", '(tags := "gh-1)'):
            with self.subTest(bad=bad):
                diags = self.node(bad)
                self.assertTrue(any("malformed (tags" in str(d) for d in diags), [str(d) for d in diags])

    def test_repeated_tags_option(self):
        self.assertErrors(self.node('(tags := "gh-1") (tags := "gh-2")'), 1, "more than one (tags")

    # placement
    def test_issue_tag_on_non_statement(self):
        self.assertErrors(self.node('(tags := "gh-5")', kind="example"), 1, "issue tags on a `example` block")

    def test_issue_tag_on_nested_proof(self):
        self.chapter(
            """
            ::::theorem "thm" (tags := "gh-5")
            Statement.
            :::proof "thm" (tags := "gh-5")
            Proof text.
            :::
            ::::
            """
        )
        diags = self.run_lint()
        self.assertErrors(diags, 1, "issue tags on a `proof` block")
        self.assertEqual(diags[0].line, 3)

    # retired footer
    def test_legacy_footer_is_error(self):
        self.assertErrors(self.node('(tags := "gh-5")', body=f"Text. {FOOTER}"), 1, "footer role was retired")

    def test_legacy_footer_outside_directive(self):
        self.chapter(FOOTER + "\n")
        self.assertErrors(self.run_lint(), 1, "outside any directive")

    def test_legacy_footer_inside_fence_ignored(self):
        self.assertEqual(self.node('(tags := "gh-5")', body=f"```\n{FOOTER}\n```"), [])

    def test_four_backtick_fence_contains_three_backticks(self):
        self.assertEqual(self.node('(tags := "gh-5")', body=f"````\n```\n{FOOTER}\n````"), [])

    # structure
    def test_unclosed_fence(self):
        self.assertErrors(self.node("", body="```\nText."), 2, "code fence open at end of file", "unclosed directive")

    def test_unclosed_directive(self):
        self.chapter('::::definition "lbl" (tags := "gh-1")\nText.\n')
        self.assertErrors(self.run_lint(), 1, "unclosed directive definition")

    def test_indented_opener(self):
        self.chapter('::::definition "lbl"\n  :::proof "x"\n  :::\n::::\n')
        diags = self.run_lint()
        self.assertTrue(any("indented directive opener" in str(d) for d in diags), [str(d) for d in diags])

    def test_multiline_opener_with_tag_passes(self):
        self.chapter(
            """
            ::::definition "lbl" (lean := "A.b,
            A.c") (tags := "gh-3")
            Text.
            ::::
            """
        )
        self.assertEqual(self.run_lint(), [])

    def test_opener_never_balances(self):
        self.chapter('::::definition "lbl" (lean := "A.b,\nText.\n::::\n')
        self.assertErrors(self.run_lint(), 2, "unbalanced parentheses", "unclosed directive")

    def test_closer_mismatch(self):
        self.chapter('::::definition "lbl"\nText.\n:::\n::::\n')
        self.assertErrors(self.run_lint(), 1, "does not match innermost directive")


if __name__ == "__main__":
    unittest.main()
