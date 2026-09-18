"""Tests for manifest parsing in scripts/aggregate-blueprint-status.py (standard library unittest only)."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load_aggregate():
    spec = importlib.util.spec_from_file_location("aggregate_blueprint_status", SCRIPTS / "aggregate-blueprint-status.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


aggregate = load_aggregate()


def decl(name: str, proved: bool = True, present: bool | None = True) -> dict:
    entry = {"canonical": name, "provedStatus": "proved" if proved else "sorried"}
    if present is not None:
        entry["present"] = present
    return entry


class CodeDeclsTest(unittest.TestCase):
    def test_new_schema_reads_all_three_lists(self):
        # The live manifest keeps every literate list empty, so a silently
        # dropped list would not show up there; assert on distinct entries.
        entry = {
            "codeData": {
                "literateDeclarations": {
                    "definedDefs": [decl("litDef", present=None)],
                    "definedTheorems": [decl("litThm", present=None)],
                },
                "externalDecls": [decl("extDecl")],
            }
        }
        names = [d["canonical"] for d in aggregate.code_decls(entry)]
        self.assertEqual(names, ["litDef", "litThm", "extDecl"])

    def test_new_schema_tolerates_missing_lists(self):
        entry = {"codeData": {"externalDecls": [decl("extOnly")]}}
        self.assertEqual([d["canonical"] for d in aggregate.code_decls(entry)], ["extOnly"])
        self.assertEqual(aggregate.code_decls({"codeData": {}}), [])
        self.assertEqual(aggregate.code_decls({}), [])

    def test_malformed_literate_declarations_fails_loudly(self):
        # Falling back to "no declarations" would leave the proved external
        # declaration alone to classify the atom as verified.
        entry = {
            "label": "thm:mixed",
            "codeData": {
                "literateDeclarations": ["unexpected-shape"],
                "externalDecls": [decl("extThm")],
            },
        }
        with self.assertRaises(SystemExit):
            aggregate.code_decls(entry)

    def test_legacy_external_schema_still_parses(self):
        entry = {"codeData": {"external": {"decls": [decl("oldExt")]}}}
        self.assertEqual([d["canonical"] for d in aggregate.code_decls(entry)], ["oldExt"])

    def test_legacy_inline_schema_still_parses(self):
        entry = {
            "codeData": {
                "inline": {
                    "definedDefs": [decl("oldDef", present=None)],
                    "definedTheorems": [decl("oldThm", present=None)],
                }
            }
        }
        self.assertEqual([d["canonical"] for d in aggregate.code_decls(entry)], ["oldDef", "oldThm"])


class ClassifyTest(unittest.TestCase):
    def test_mixed_sources_with_one_unproved_declaration(self):
        entry = {
            "kind": "theorem",
            "label": "thm:mixed",
            "codeData": {
                "literateDeclarations": {"definedDefs": [], "definedTheorems": [decl("litThm", present=None)]},
                "externalDecls": [decl("extThm", proved=False)],
            },
        }
        atom = aggregate.classify(entry, "Secure-Messaging")
        self.assertTrue(atom.specified)
        self.assertFalse(atom.verified)

    def test_absent_external_declaration_is_not_proved(self):
        entry = {
            "kind": "definition",
            "label": "def:absent",
            "codeData": {"externalDecls": [decl("missing", present=False)]},
        }
        atom = aggregate.classify(entry, "Secure-Messaging")
        self.assertTrue(atom.specified)
        self.assertFalse(atom.verified)

    def test_inline_declaration_without_present_field_counts_as_proved(self):
        entry = {
            "kind": "definition",
            "label": "def:inline",
            "codeData": {"literateDeclarations": {"definedDefs": [decl("litDef", present=None)], "definedTheorems": []}},
        }
        atom = aggregate.classify(entry, "Secure-Messaging")
        self.assertTrue(atom.specified)
        self.assertTrue(atom.verified)


if __name__ == "__main__":
    unittest.main()
