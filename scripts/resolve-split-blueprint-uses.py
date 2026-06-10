#!/usr/bin/env python3
"""Resolve cross-chapter Blueprint `uses` links after split rendering.

Verso can resolve `uses` references within one rendered manual, but our site is
assembled from independently rendered chapter manuals. This script stitches those
manuals back together by reading source `uses` metadata and rendered preview
manifests, then replacing cross-chapter `[??]` placeholders in the final HTML.
"""

import argparse
import html
import json
import os
import re
from dataclasses import dataclass
from pathlib import Path


MANIFEST_PATH = "-verso-data/blueprint-preview-manifest.json"
ATOM_BLOCK_RE = re.compile(
    r'^(?P<fence>:{3,})(?P<kind>definition|theorem)\s+"(?P<label>[^"]+)".*?^\1\s*$',
    re.MULTILINE | re.DOTALL,
)
USES_RE = re.compile(r'\{uses\s+"([^"]+)"\}')


@dataclass(frozen=True)
class AtomTarget:
    label: str
    title: str
    chapter: str
    href: str


def load_source_uses(docs_dir: Path) -> dict[str, list[str]]:
    # Source blocks preserve the authored order of `{uses ...}` references, which
    # lets us replace the rendered `[??]` placeholders in the same order.
    uses_by_label: dict[str, list[str]] = {}
    for source in sorted(docs_dir.rglob("*.lean")):
        text = source.read_text()
        for match in ATOM_BLOCK_RE.finditer(text):
            uses = USES_RE.findall(match.group(0))
            if uses:
                uses_by_label[match.group("label")] = uses
    return uses_by_label


def load_targets(site_dir: Path) -> dict[str, AtomTarget]:
    # Rendered manifests provide the final display title and local href for every
    # Blueprint atom. We index them globally by label across all chapters.
    targets: dict[str, AtomTarget] = {}
    duplicates: set[str] = set()
    for manifest in sorted(site_dir.glob(f"*/{MANIFEST_PATH}")):
        chapter = manifest.relative_to(site_dir).parts[0]
        data = json.loads(manifest.read_text())
        for entry in data.get("previews", []):
            if entry.get("targetKind") != "block":
                continue
            if entry.get("kind") not in {"definition", "theorem"}:
                continue
            label = entry.get("label", "")
            href = entry.get("href", "")
            if not label or not href:
                continue
            if label in targets:
                duplicates.add(label)
            targets[label] = AtomTarget(
                label=label,
                title=entry.get("title", label),
                chapter=chapter,
                href=href,
            )
    if duplicates:
        duplicate_list = ", ".join(sorted(duplicates))
        raise SystemExit(f"Duplicate blueprint labels found: {duplicate_list}")
    return targets


def link_base_dir(html_file: Path, text: str) -> Path:
    match = re.search(r'<base\s+href="([^"]*)"', text)
    if not match:
        return html_file.parent

    # Verso pages set a relative <base> so chapter-local assets and links resolve
    # from the chapter root. Cross-chapter links must be relative to that same
    # base; otherwise GitHub Pages project paths can be escaped accidentally.
    base_href = html.unescape(match.group(1))
    if re.match(r"^[A-Za-z][A-Za-z0-9+.-]*:", base_href) or base_href.startswith("/"):
        return html_file.parent
    base_path = base_href.partition("#")[0].partition("?")[0]
    if not base_path:
        return html_file.parent
    return html_file.parent / base_path


def relative_href(site_dir: Path, link_base: Path, target: AtomTarget) -> str:
    href, sep, fragment = target.href.partition("#")
    target_path = site_dir / target.chapter / href
    rel = os.path.relpath(target_path, link_base)

    # Directory-style Verso hrefs need the trailing slash before the fragment so
    # browsers resolve `chapter/page/#anchor`, not `chapter/page#anchor`.
    if href.endswith("/") and not rel.endswith("/"):
        rel += "/"
    return rel + (sep + fragment if sep else "")


def replacement_for(site_dir: Path, link_base: Path, target: AtomTarget) -> str:
    href = html.escape(relative_href(site_dir, link_base, target), quote=True)
    title = html.escape(target.title)
    label = html.escape(target.label, quote=True)
    return f'<span><a class="split-blueprint-use" href="{href}" title="{label}">{title}</a></span>'


def replace_unresolved_uses(block: str, replacements: list[str]) -> tuple[str, int]:
    replaced = 0

    def replace_one(match: re.Match[str]) -> str:
        nonlocal replaced
        if replaced >= len(replacements):
            return match.group(0)
        value = replacements[replaced]
        replaced += 1
        return value

    return re.sub(r'<span>\[\?\?\]</span>', replace_one, block), replaced


def process_html_file(
    html_file: Path,
    site_dir: Path,
    uses_by_label: dict[str, list[str]],
    targets: dict[str, AtomTarget],
) -> int:
    text = html_file.read_text()
    try:
        current_chapter = html_file.relative_to(site_dir).parts[0]
    except ValueError:
        return 0
    link_base = link_base_dir(html_file, text)

    total_replaced = 0
    output: list[str] = []
    cursor = 0
    marker = '<div class="bp_wrapper'
    while True:
        start = text.find(marker, cursor)
        if start == -1:
            output.append(text[cursor:])
            break
        next_start = text.find(marker, start + len(marker))
        end = next_start if next_start != -1 else len(text)
        output.append(text[cursor:start])
        block = text[start:end]
        title_match = re.search(r'\stitle="([^"]+)"', block)
        if title_match:
            label = html.unescape(title_match.group(1))
            deps = uses_by_label.get(label, [])

            # Same-chapter dependencies are already resolved by Verso. Only the
            # cross-chapter dependencies should correspond to `[??]` slots here.
            replacements = [
                replacement_for(site_dir, link_base, targets[dep])
                for dep in deps
                if dep in targets and targets[dep].chapter != current_chapter
            ]
            if replacements and '<span>[??]</span>' in block:
                block, replaced = replace_unresolved_uses(block, replacements)
                total_replaced += replaced
        output.append(block)
        cursor = end

    if total_replaced:
        html_file.write_text("".join(output))
    return total_replaced


def main() -> None:
    parser = argparse.ArgumentParser(description="Resolve cross-chapter Blueprint uses in a split Verso site.")
    parser.add_argument("--site-dir", type=Path, default=Path("_out/site/html-multi"))
    parser.add_argument("--docs-dir", type=Path, default=Path("docs/SecureMessagingDocs/Chapters"))
    args = parser.parse_args()

    uses_by_label = load_source_uses(args.docs_dir)
    targets = load_targets(args.site_dir)
    replaced = 0
    for html_file in sorted(args.site_dir.glob("**/*.html")):
        if html_file == args.site_dir / "index.html":
            continue
        replaced += process_html_file(html_file, args.site_dir, uses_by_label, targets)
    print(f"Resolved {replaced} split Blueprint uses link(s).")


if __name__ == "__main__":
    main()