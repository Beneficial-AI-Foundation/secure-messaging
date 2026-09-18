"""Tests for the tripwire and history prune in scripts/update-blueprint-progress-history.py (standard library unittest only)."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load_update():
    spec = importlib.util.spec_from_file_location(
        "update_blueprint_progress_history", SCRIPTS / "update-blueprint-progress-history.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


update = load_update()


def snapshot(commit: str, defs: tuple[int, int], thms: tuple[int, int], source: str = "rendered-blueprint-manifest") -> dict:
    return {
        "commit": commit,
        "date": f"2026-09-{len(commit):02d}T00:00:00+00:00",
        "source": source,
        "definitions": {"total": defs[0], "specified": defs[1], "specifiedLabels": [], "verified": 0, "verifiedLabels": []},
        "theorems": {"total": thms[0], "specified": thms[1], "specifiedLabels": [], "verified": 0, "verifiedLabels": []},
    }


def manifest_entry(label: str, kind: str, decls: list[dict]) -> dict:
    return {
        "targetKind": "block",
        "kind": kind,
        "label": label,
        "title": "",
        "href": "Secure-Messaging/index.html",
        "tags": ["gh-1"],
        "codeData": {"externalDecls": decls},
    }


def write_site(tmp: Path, entries: list[dict]) -> Path:
    manifest = tmp / "-verso-data" / "blueprint-manifest.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(json.dumps({"previews": entries}))
    return tmp


class PruneTest(unittest.TestCase):
    def test_merge_drops_poisoned_snapshots_and_keeps_the_rest(self):
        good = snapshot("aaaa", (63, 37), (60, 13))
        poisoned = snapshot("bbbbb", (63, 0), (60, 0))
        # Estimated seeds start with zero totals; a zero-specified seed with
        # positive totals is not from the broken parser either.
        seeded_empty = snapshot("cc", (0, 0), (0, 0), source="github-issue-closures")
        seeded_zero = snapshot("ddd", (63, 0), (60, 0), source="github-issue-closures")
        existing = {"snapshots": [good, poisoned, seeded_empty, seeded_zero]}
        current = snapshot("eeeeee", (63, 37), (60, 13))
        merged = update.merge_history(existing, current)
        self.assertEqual(
            [entry["commit"] for entry in merged["snapshots"]],
            ["cc", "ddd", "aaaa", "eeeeee"],
        )

    def test_zero_specified_in_one_kind_only_is_kept(self):
        one_kind = snapshot("aaaa", (63, 37), (60, 0))
        merged = update.merge_history({"snapshots": [one_kind]}, snapshot("bbbbb", (63, 37), (60, 13)))
        self.assertIn("aaaa", [entry["commit"] for entry in merged["snapshots"]])


class TripwireTest(unittest.TestCase):
    def current_snapshot(self, entries: list[dict]) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            site = write_site(Path(tmp), entries)
            return update.current_snapshot(site, "0" * 40, "2026-09-18T00:00:00+00:00", "test")

    def test_all_unspecified_render_refuses_to_snapshot(self):
        # The demonstrated failure: the parser recognizes no declarations at
        # all, so every tracked atom reads unspecified.
        entries = [
            manifest_entry("def:a", "definition", []),
            manifest_entry("thm:b", "theorem", []),
        ]
        with self.assertRaises(SystemExit):
            self.current_snapshot(entries)

    def test_empty_tracked_set_refuses_to_snapshot(self):
        # A drift that hides the tracked set entirely (tags or kinds moving)
        # must not publish an all-zero snapshot: the prune could not remove it
        # later because both totals read zero.
        with self.assertRaises(SystemExit):
            self.current_snapshot([])

    def test_partially_specified_render_snapshots_normally(self):
        entries = [
            manifest_entry("def:a", "definition", [{"canonical": "a", "present": True, "provedStatus": "proved"}]),
            manifest_entry("thm:b", "theorem", []),
        ]
        result = self.current_snapshot(entries)
        self.assertEqual(result["definitions"]["specified"], 1)
        self.assertEqual(result["theorems"]["specified"], 0)


if __name__ == "__main__":
    unittest.main()
