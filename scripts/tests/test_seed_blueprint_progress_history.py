"""Tests for the source scan of scripts/seed-blueprint-progress-history.py (standard library unittest only)."""

from __future__ import annotations

import importlib.util
import sys
import textwrap
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load_seed():
    spec = importlib.util.spec_from_file_location("seed_blueprint_progress_history", SCRIPTS / "seed-blueprint-progress-history.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


seed = load_seed()


def atoms(text: str) -> dict[str, set[int]]:
    lines = textwrap.dedent(text).lstrip("\n").splitlines()
    return {label: seed.block_issues(block) for _kind, label, block in seed.iter_atom_blocks(lines)}


class SeedScanTest(unittest.TestCase):
    def test_tag_on_opener_and_legacy_footer_both_count(self):
        self.assertEqual(
            atoms(
                """
                ::::definition "a" (tags := "gh-1")
                Text.
                ::::
                ::::theorem "b"
                {githubLabel}`github` {githubIssue 2}[]
                ::::
                """
            ),
            {"a": {1}, "b": {2}},
        )

    def test_fenced_example_directive_is_not_an_atom(self):
        self.assertEqual(
            atoms(
                """
                Prose.
                ```
                :::definition "fake" (tags := "gh-999")
                :::
                ```
                ::::definition "real" (tags := "gh-1")
                ::::
                """
            ),
            {"real": {1}},
        )

    def test_fenced_footer_inside_a_node_does_not_count(self):
        self.assertEqual(
            atoms(
                """
                ::::definition "real" (tags := "gh-1")
                ````
                {githubIssue 999}[]
                ```
                ::::
                ````
                ::::
                """
            ),
            {"real": {1}},
        )

    def test_tracked_labels_follow_the_same_rule(self):
        text = textwrap.dedent(
            """
            ```
            :::theorem "fake" (tags := "gh-9")
            :::
            ```
            ::::theorem "real" (tags := "gh-1")
            ::::
            ::::theorem "untracked"
            ::::
            """
        )
        self.assertEqual(seed.tracked_labels_in_source(text), {"real"})


if __name__ == "__main__":
    unittest.main()
