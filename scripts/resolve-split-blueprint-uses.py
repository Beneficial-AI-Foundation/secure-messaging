#!/usr/bin/env python3

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
    uses_by_label: dict[str, list[str]] = {}
    for source in sorted(docs_dir.rglob("*.lean")):
        text = source.read_text()
        for match in ATOM_BLOCK_RE.finditer(text):
            uses = USES_RE.findall(match.group(0))
            if uses:
                uses_by_label[match.group("label")] = uses
    return uses_by_label


def load_targets(site_dir: Path) -> dict[str, AtomTarget]:
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


def relative_href(site_dir: Path, html_file: Path, target: AtomTarget) -> str:
    href, sep, fragment = target.href.partition("#")
    target_path = site_dir / target.chapter / href
    rel = os.path.relpath(target_path, html_file.parent)
    if href.endswith("/") and not rel.endswith("/"):
        rel += "/"
    return rel + (sep + fragment if sep else "")


def replacement_for(site_dir: Path, html_file: Path, target: AtomTarget) -> str:
    href = html.escape(relative_href(site_dir, html_file, target), quote=True)
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
            replacements = [
                replacement_for(site_dir, html_file, targets[dep])
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