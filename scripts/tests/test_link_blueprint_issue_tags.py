"""Tests for scripts/link-blueprint-issue-tags.py (standard library unittest only).

The fixtures are fragments of a raw verso-blueprint v4.33.0 render, taken before
the link pass ran: the node wrapper and metadata panel from a chapter page, and
the rollup-head and item badges from a Blueprint Summary page.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load_link():
    spec = importlib.util.spec_from_file_location("link_blueprint_issue_tags", SCRIPTS / "link-blueprint-issue-tags.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


link = load_link()
REPO = "Beneficial-AI-Foundation/secure-messaging"
ISSUES = f"https://github.com/{REPO}/issues"
PAGE = "Authenticated-Encryption-with-Associated-Data/AEAD-Definitions/"


def anchor(number: int, text: str) -> str:
    return (
        f'<a class="github-issue-link" href="{ISSUES}/{number}" '
        f'target="_blank" rel="noopener noreferrer">{text}</a>'
    )


def chips(*contents: str) -> str:
    return "".join(f'<span class="bp_metadata_tag">{c}</span>' for c in contents)


def item(key: str, chip_markup: str) -> str:
    return (
        f'<span class="bp_metadata_item"><span class="bp_metadata_key">{key}</span>'
        f'<span class="bp_metadata_tags">{chip_markup}</span></span>'
    )


def node(label: str, panel_items: str | None) -> str:
    """A node wrapper as rendered on a chapter page; nodes without metadata have no panel."""
    panel = f'\n<div class="bp_metadata_panel">\n{panel_items}</div>' if panel_items is not None else ""
    return (
        f'<div class="bp_wrapper bp_kind_definition_wrapper definition_thmwrapper theorem-style-definition '
        f'bp_kind_definition bp_style_definition" title="{label}" id="--informal-preview-{label}--statement">\n'
        f'<div class="bp_heading bp_kind_definition_heading definition_thmheading">\n'
        f'<span class="bp_caption">Definition</span></div>{panel}\n'
        f'<div class="bp_content bp_kind_definition_content definition_thmcontent">\n<p>Text.</p></div></div>\n'
    )


def rollup_head(badge: str) -> str:
    return (
        '<li class="bp_summary_item">\n<div class="bp_summary_item_top">\n'
        f'<span class="bp_summary_item_head">{badge}</span></div>\n'
        '<div class="bp_summary_badge_row">\n<span class="bp_summary_badge">entries: 1</span>'
        '<span class="bp_summary_badge bp_summary_badge_warn">actionable: 0</span></div>\n</li>\n'
    )


def summary_item(label: str, badge: str) -> str:
    return (
        '<li class="bp_summary_item">\n<div class="bp_summary_item_top">\n'
        f'<span class="bp_summary_item_head"><a href="{PAGE}#--informal-preview-{label}--statement">'
        f'<code>{label}</code></a></span><span class="bp_summary_item_meta">(Definition)</span></div>\n'
        '<div class="bp_summary_item_body">\nMissing owner metadata.</div>\n'
        f'<div class="bp_summary_badge_row">\n{badge}</div>\n</li>\n'
    )


def raw_head(number: int) -> str:
    return f'<span class="bp_summary_badge bp_summary_badge_warn">tag: gh-{number}</span>'


def raw_badge(number: int) -> str:
    return f'<span class="bp_summary_badge">tag: gh-{number}</span>'


def linked_head(number: int) -> str:
    return f'<span class="bp_summary_badge bp_summary_badge_warn">{anchor(number, f"GitHub #{number}")}</span>'


def linked_badge(number: int) -> str:
    return f'<span class="bp_summary_badge">{anchor(number, f"GitHub #{number}")}</span>'


def summary_page(heads: list[int], items: list[tuple[str, int]], linked: bool = False) -> str:
    head = linked_head if linked else raw_head
    badge = linked_badge if linked else raw_badge
    return (
        "<html><body><h1>Blueprint Summary</h1>\n"
        '<details class="bp_summary_subsection"><summary>Most used in statements (1)</summary><ul class="bp_summary_list">\n'
        + summary_item("aead", '<span class="bp_summary_badge bp_summary_badge_warn">statement uses: 24</span>'
                       '<span class="bp_summary_badge">proof uses: 0</span>')
        + "</ul></details>\n"
        f'<details class="bp_summary_subsection"><summary>Tag rollups ({len(heads)})</summary><ul class="bp_summary_list">\n'
        + "".join(rollup_head(head(n)) for n in heads)
        + "</ul></details>\n"
        '<details class="bp_summary_nested"><summary>Missing owner (4)</summary><ul class="bp_summary_list">\n'
        + "".join(summary_item(label, badge(n)) for label, n in items)
        + "</ul></details>\n</body></html>\n"
    )


def block(label: str, tags: list[str], target_kind: str = "block") -> dict:
    return {
        "href": f"{PAGE}#--informal-preview-{label}--statement",
        "key": f"{label}--statement",
        "label": label,
        "tags": tags,
        "targetKind": target_kind,
    }


BLOCKS = [
    block("aead", ["gh-192"]),
    block("aead_oracles", ["gh-192"]),
    block("aead_mixed", ["gh-5", "c&d"]),
    block("aead_untagged", []),
    block("aead", [], target_kind="preview"),
]
HEADS = [5, 192]
ITEMS = [("aead", 192), ("aead_oracles", 192), ("aead_mixed", 5), ("aead", 192)]


def raw_chapter() -> str:
    return (
        "<html><body>\n"
        + node("aead", item("Tags", chips("gh-192")))
        + node("aead_oracles", item("Tags", chips("gh-192")))
        + node("aead_mixed", item("Tags", chips("gh-5", "c&amp;d")))
        + node("aead_untagged", None)
        + "</body></html>\n"
    )


class LinkTest(unittest.TestCase):
    def setUp(self):
        self.site = Path(tempfile.mkdtemp()) / "html-multi"
        self.site.mkdir()

    def write(self, relative: str, text: str) -> Path:
        path = self.site / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def manifest(self, blocks=BLOCKS):
        self.write("-verso-data/blueprint-manifest.json", json.dumps({"previews": blocks}))

    def summaries(self, heads=HEADS, items=ITEMS, linked=False):
        for relative in ("Blueprint-Summary/index.html", "Authenticated-Encryption-with-Associated-Data/Blueprint-Summary/index.html"):
            self.write(relative, summary_page(heads, items, linked))

    def site_files(self):
        return {p.relative_to(self.site): p.read_bytes() for p in sorted(self.site.rglob("*")) if p.is_file()}

    def raw_site(self):
        self.manifest()
        self.write(PAGE + "index.html", raw_chapter())
        self.summaries()
        self.write("index.html", "<html><body><h1>Secure Messaging</h1><p>tag: none</p></body></html>\n")

    def run_link(self, repository=REPO):
        with contextlib.redirect_stdout(io.StringIO()):
            return link.main(["--site-dir", str(self.site), "--repository", repository])

    def read(self, relative: str) -> str:
        return (self.site / relative).read_text()

    # rewriting
    def test_all_issue_item_is_labelled_github(self):
        self.raw_site()
        self.assertEqual(self.run_link(), 0)
        page = self.read(PAGE + "index.html")
        self.assertIn(item("GitHub", chips(anchor(192, "#192"))), page)
        self.assertEqual(page.count('bp_metadata_key">GitHub<'), 2)
        self.assertEqual(page.count('bp_metadata_key">Tags<'), 1, "only the mixed item keeps the Tags label")

    def test_mixed_item_keeps_tags_label_and_other_chips(self):
        self.raw_site()
        self.assertEqual(self.run_link(), 0)
        page = self.read(PAGE + "index.html")
        self.assertIn(item("Tags", chips(anchor(5, "GitHub #5"), "c&amp;d")), page)

    def test_two_blocks_sharing_an_issue_both_validate(self):
        self.raw_site()
        self.assertEqual(self.run_link(), 0)
        self.assertEqual(self.read(PAGE + "index.html").count(anchor(192, "#192")), 2)

    def test_summary_badges_linked_on_every_page(self):
        self.raw_site()
        self.assertEqual(self.run_link(), 0)
        for relative in ("Blueprint-Summary/index.html", "Authenticated-Encryption-with-Associated-Data/Blueprint-Summary/index.html"):
            page = self.read(relative)
            self.assertNotIn("tag: gh-", page)
            self.assertIn(linked_head(192), page)
            self.assertIn(linked_head(5), page)
            self.assertEqual(page.count(linked_badge(192)), 3)
            self.assertEqual(page.count(linked_badge(5)), 1)
            self.assertIn('<span class="bp_summary_badge bp_summary_badge_warn">statement uses: 24</span>', page)

    def test_idempotent(self):
        self.raw_site()
        self.assertEqual(self.run_link(), 0)
        first = self.site_files()
        self.assertEqual(self.run_link(), 0)
        self.assertEqual(self.site_files(), first)

    def test_half_linked_state_is_completed(self):
        self.manifest()
        self.write(
            PAGE + "index.html",
            "<html><body>\n"
            + node("aead", item("Tags", chips(anchor(192, "#192"))))
            + node("aead_oracles", item("Tags", chips(anchor(192, "#192"))))
            + node("aead_mixed", item("Tags", chips(anchor(5, "#5"), "c&amp;d")))
            + node("aead_untagged", None)
            + "</body></html>\n",
        )
        self.summaries()
        self.assertEqual(self.run_link(), 0)
        page = self.read(PAGE + "index.html")
        self.assertEqual(page.count(item("GitHub", chips(anchor(192, "#192")))), 2)
        self.assertIn(item("Tags", chips(anchor(5, "GitHub #5"), "c&amp;d")), page)
        self.assertNotIn("tag: gh-", self.read("Blueprint-Summary/index.html"))

    def test_site_without_issue_tags_is_left_alone(self):
        self.manifest([block("aead", []), block("aead_oracles", ["draft"])])
        self.write(PAGE + "index.html", "<html><body>\n" + node("aead", None) + node("aead_oracles", item("Tags", chips("draft"))) + "</body></html>\n")
        self.summaries(heads=[], items=[])
        before = self.site_files()
        self.assertEqual(self.run_link(), 0)
        self.assertEqual(self.site_files(), before)

    # validation
    def assertRejected(self, *fragments: str):
        before = self.site_files()
        with contextlib.redirect_stderr(io.StringIO()) as stderr:
            self.assertEqual(self.run_link(), 1)
        for fragment in fragments:
            self.assertIn(fragment, stderr.getvalue())
        self.assertEqual(self.site_files(), before, "a failed run must not rewrite any file")

    def test_swapped_numbers_with_unchanged_totals_are_rejected(self):
        self.manifest([block("aead", ["gh-192"]), block("aead_oracles", ["gh-193"])])
        self.write(
            PAGE + "index.html",
            "<html><body>\n" + node("aead", item("Tags", chips("gh-193"))) + node("aead_oracles", item("Tags", chips("gh-192"))) + "</body></html>\n",
        )
        self.summaries(heads=[192, 193], items=[("aead", 192), ("aead_oracles", 193)])
        self.assertRejected("block " + PAGE + "#--informal-preview-aead--statement", "linked issues [193] do not match the manifest tags [192]")

    def test_summary_page_missing_item_badges_is_rejected(self):
        self.raw_site()
        self.write("Authenticated-Encryption-with-Associated-Data/Blueprint-Summary/index.html", summary_page(HEADS, []))
        self.assertRejected("Authenticated-Encryption-with-Associated-Data/Blueprint-Summary/index.html", "item badges link 0 badges")

    def test_leftover_raw_badge_is_rejected(self):
        self.raw_site()
        self.write(
            "Blueprint-Summary/index.html",
            summary_page(HEADS, ITEMS).replace(raw_badge(5), '<span class="bp_summary_badge bp_summary_badge_other">tag: gh-5</span>'),
        )
        self.assertRejected("Blueprint-Summary/index.html: a raw `tag: gh-` badge remains")

    def test_leftover_raw_chip_is_rejected(self):
        self.raw_site()
        self.write("index.html", "<html><body>" + item("Labels", chips("gh-192")) + "</body></html>\n")
        self.assertRejected("index.html: a raw issue chip remains")

    def test_missing_panel_is_rejected(self):
        self.raw_site()
        self.write(PAGE + "index.html", raw_chapter().replace(item("Tags", chips("gh-192")), "", 1))
        self.assertRejected("expected one tag item")

    def test_extra_tag_item_is_rejected(self):
        self.raw_site()
        self.write("index.html", "<html><body>" + item("Tags", chips("draft")) + "</body></html>\n")
        self.assertRejected("found 4 tag items site-wide but the manifest has 3 tagged blocks")

    # usage errors
    def test_missing_manifest_is_a_usage_error(self):
        self.write(PAGE + "index.html", raw_chapter())
        before = self.site_files()
        with self.assertRaises(SystemExit) as raised, contextlib.redirect_stderr(io.StringIO()):
            self.run_link()
        self.assertEqual(raised.exception.code, 2)
        self.assertEqual(self.site_files(), before)

    def test_malformed_repository_is_a_usage_error(self):
        self.raw_site()
        before = self.site_files()
        for bad in ("owner", "owner/name/extra", "owner/na me", "/name", "owner/"):
            with self.subTest(bad=bad), self.assertRaises(SystemExit) as raised, contextlib.redirect_stderr(io.StringIO()):
                self.run_link(repository=bad)
            self.assertEqual(raised.exception.code, 2)
        self.assertEqual(self.site_files(), before)


if __name__ == "__main__":
    unittest.main()
