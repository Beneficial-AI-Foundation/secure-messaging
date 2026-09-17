#!/usr/bin/env python3
"""Link the GitHub issue tags in a rendered blueprint site.

verso-blueprint renders a node's `gh-<n>` tags as plain chips under a hard-coded
`Tags` label in the node's metadata panel, and as `tag: gh-<n>` badges on the
Blueprint Summary pages. This post-render pass, run by `render-docs-site.sh`,
rewrites both surfaces:

- a metadata item whose chips are all issue tags is relabelled `GitHub` and each
  chip becomes a link reading `#<n>`; an item that also carries other tags keeps
  the `Tags` label, links its issue chips as `GitHub #<n>` and leaves the other
  chips byte for byte;
- every summary badge `tag: gh-<n>` becomes a link reading `GitHub #<n>`, with
  its class attribute unchanged.

The pass recognises its own output, so it is idempotent. Before writing, it
validates the final state of every page against `blueprint-manifest.json`: for
each `block` entry with issue tags it locates the node by the fragment of its
`href`, reads the first metadata panel inside that node and requires the linked
issue numbers to equal the block's tags; site-wide, no raw issue chip may
remain and the number of tag items must equal the number of tagged blocks;
each Summary page must link one rollup head per distinct issue, at least one
item badge per node tagged with the issue, exactly the manifest's set of issues, and no `tag:
gh-` text. Any violation fails the run and leaves every file untouched, so a
verso-blueprint upgrade that changes either markup cannot drop the links.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

ISSUE_TAG = re.compile(r"gh-([1-9][0-9]*)")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")

# An anchor produced by this pass (either text form). The issue number is read
# from the href; the text must name the same number.
ANCHOR = (
    r'<a class="github-issue-link" href="https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+'
    r'/issues/(?P<{n}>[1-9][0-9]*)" target="_blank" rel="noopener noreferrer">'
    r"(?:GitHub )?#(?P={n})</a>"
)
CHIP = re.compile(
    r'<span class="bp_metadata_tag">(?P<content>[^<]*|' + ANCHOR.format(n="anchor") + r")</span>"
)
ITEM = re.compile(
    r'<span class="bp_metadata_item"><span class="bp_metadata_key">(?P<key>Tags|GitHub)</span>'
    r'<span class="bp_metadata_tags">(?P<chips>(?:<span class="bp_metadata_tag">'
    r"(?:[^<]*|" + ANCHOR.format(n="c") + r")</span>)+)</span></span>"
)
BADGE = re.compile(
    r'<span class="(?P<classes>bp_summary_badge(?: bp_summary_badge_warn)?)">'
    r"(?:tag: gh-(?P<raw>[1-9][0-9]*)|" + ANCHOR.format(n="linked") + r")</span>"
)
RAW_CHIP = re.compile(r'<span class="bp_metadata_tag">gh-[1-9][0-9]*</span>')
RAW_BADGE = re.compile(r">tag: gh-[1-9][0-9]*<")
WRAPPER = re.compile(r'<div class="bp_wrapper[ "]')
PANEL = '<div class="bp_metadata_panel">'


class UsageError(Exception):
    pass


class ValidationError(Exception):
    pass


@dataclass(frozen=True)
class Block:
    href: str
    tags: tuple[str, ...]

    @property
    def issues(self) -> tuple[int, ...]:
        return tuple(int(m.group(1)) for tag in self.tags if (m := ISSUE_TAG.fullmatch(tag)))

    @property
    def page(self) -> str:
        path = self.href.split("#", 1)[0]
        return path + "index.html" if path.endswith("/") or not path else path

    @property
    def fragment(self) -> str:
        return self.href.split("#", 1)[1] if "#" in self.href else ""


def load_blocks(site_dir: Path) -> list[Block]:
    manifest_path = site_dir / "-verso-data" / "blueprint-manifest.json"
    if not manifest_path.is_file():
        raise UsageError(f"no manifest at {manifest_path}")
    manifest = json.loads(manifest_path.read_bytes())
    return [
        Block(entry["href"], tuple(entry.get("tags", [])))
        for entry in manifest.get("previews", [])
        if entry.get("targetKind") == "block"
    ]


def anchor(repository: str, number: int, text: str) -> str:
    return (
        f'<a class="github-issue-link" href="https://github.com/{repository}/issues/{number}" '
        f'target="_blank" rel="noopener noreferrer">{text}</a>'
    )


def chip_issue(match: re.Match) -> int | None:
    """The issue number of a chip, or None for a chip that is not an issue tag."""
    if match.group("anchor"):
        return int(match.group("anchor"))
    raw = ISSUE_TAG.fullmatch(match.group("content"))
    return int(raw.group(1)) if raw else None


def rewrite_item(match: re.Match, repository: str) -> str:
    chips = list(CHIP.finditer(match.group("chips")))
    issues = [chip_issue(chip) for chip in chips]
    all_issues = all(number is not None for number in issues)
    key = "GitHub" if all_issues else "Tags"
    rendered = []
    for chip, number in zip(chips, issues):
        if number is None:
            rendered.append(chip.group(0))
        else:
            text = f"#{number}" if all_issues else f"GitHub #{number}"
            rendered.append(f'<span class="bp_metadata_tag">{anchor(repository, number, text)}</span>')
    return (
        f'<span class="bp_metadata_item"><span class="bp_metadata_key">{key}</span>'
        f'<span class="bp_metadata_tags">{"".join(rendered)}</span></span>'
    )


def rewrite_badge(match: re.Match, repository: str) -> str:
    number = int(match.group("raw") or match.group("linked"))
    return f'<span class="{match.group("classes")}">{anchor(repository, number, f"GitHub #{number}")}</span>'


def transform(text: str, repository: str) -> str:
    text = ITEM.sub(lambda m: rewrite_item(m, repository), text)
    return BADGE.sub(lambda m: rewrite_badge(m, repository), text)


def is_summary_page(relative: Path) -> bool:
    return relative.name == "index.html" and relative.parent.name == "Blueprint-Summary"


def validate_panel(block: Block, pages: dict[Path, str], repository: str) -> None:
    text = pages.get(Path(block.page))
    where = f"block {block.href}"
    if text is None:
        raise ValidationError(f"{where}: page {block.page} not found")
    start = text.find(f'id="{block.fragment}"')
    if start < 0:
        raise ValidationError(f"{where}: node id not found on its page")
    following = WRAPPER.search(text, start + 1)
    end = following.start() if following else len(text)
    panel = text.find(PANEL, start, end)
    if panel < 0:
        raise ValidationError(f"{where}: no metadata panel inside the node")
    items = list(ITEM.finditer(text, panel, end))
    if len(items) != 1:
        raise ValidationError(f"{where}: expected one tag item in the node's panel, found {len(items)}")
    item = items[0]
    chips = list(CHIP.finditer(item.group("chips")))
    issues = [chip_issue(chip) for chip in chips]
    linked = sorted(
        int(chip.group("anchor")) for chip in chips if chip.group("anchor")
    )
    if linked != sorted(block.issues):
        raise ValidationError(
            f"{where}: linked issues {linked} do not match the manifest tags {sorted(block.issues)}"
        )
    if any(number is not None and not chip.group("anchor") for chip, number in zip(chips, issues)):
        raise ValidationError(f"{where}: an issue chip is not linked")
    expected_key = "GitHub" if all(number is not None for number in issues) else "Tags"
    if item.group("key") != expected_key:
        raise ValidationError(f"{where}: label is {item.group('key')!r}, expected {expected_key!r}")
    for chip in chips:
        if chip.group("anchor") and f"https://github.com/{repository}/issues/" not in chip.group(0):
            raise ValidationError(f"{where}: a chip links to another repository")


def validate(blocks: list[Block], pages: dict[Path, str], repository: str) -> None:
    tagged = [block for block in blocks if block.tags]
    with_issues = [block for block in tagged if block.issues]
    # How many nodes carry each issue: the Summary must show at least that many item badges for it.
    expected = Counter(number for block in with_issues for number in block.issues)
    gh_set = set(expected)

    for block in with_issues:
        validate_panel(block, pages, repository)

    item_count = 0
    for relative, text in pages.items():
        if RAW_CHIP.search(text):
            raise ValidationError(f"{relative}: a raw issue chip remains")
        item_count += len(ITEM.findall(text))
    if item_count != len(tagged):
        raise ValidationError(
            f"found {item_count} tag items site-wide but the manifest has {len(tagged)} tagged blocks"
        )

    summaries = {relative: text for relative, text in pages.items() if is_summary_page(relative)}
    if gh_set and not summaries:
        raise ValidationError("no Blueprint-Summary page found")
    for relative, text in summaries.items():
        if RAW_BADGE.search(text):
            raise ValidationError(f"{relative}: a raw `tag: gh-` badge remains")
        heads = Counter()
        items = Counter()
        for badge in BADGE.finditer(text):
            number = int(badge.group("linked"))
            if f"https://github.com/{repository}/issues/" not in badge.group(0):
                raise ValidationError(f"{relative}: a badge links to another repository")
            (heads if "bp_summary_badge_warn" in badge.group("classes") else items)[number] += 1
        if sorted(heads.elements()) != sorted(gh_set):
            raise ValidationError(
                f"{relative}: rollup heads link {sorted(heads.elements())}, expected one per issue in {sorted(gh_set)}"
            )
        short = {number: (items[number], count) for number, count in expected.items() if items[number] < count}
        if short or set(items) != gh_set:
            raise ValidationError(
                f"{relative}: item badges per issue {dict(sorted(items.items()))} do not cover the tagged nodes "
                f"{dict(sorted(expected.items()))}"
            )


def write_atomic(path: Path, data: bytes) -> None:
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=path.name, suffix=".tmp")
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
        shutil.copymode(path, tmp)  # mkstemp creates the file 0600
        os.replace(tmp, path)
    except BaseException:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


def run(site_dir: Path, repository: str) -> str:
    if not REPOSITORY.fullmatch(repository):
        raise UsageError(f"--repository must be owner/name, got {repository!r}")
    if not site_dir.is_dir():
        raise UsageError(f"--site-dir {site_dir} is not a directory")
    blocks = load_blocks(site_dir)

    originals: dict[Path, bytes] = {}
    pages: dict[Path, str] = {}
    for path in sorted(site_dir.rglob("*.html")):
        relative = path.relative_to(site_dir)
        originals[relative] = path.read_bytes()
        pages[relative] = transform(originals[relative].decode("utf-8"), repository)

    validate(blocks, pages, repository)

    changed = 0
    for relative, text in pages.items():
        data = text.encode("utf-8")
        if data != originals[relative]:
            write_atomic(site_dir / relative, data)
            changed += 1
    chips = sum(len(block.issues) for block in blocks)
    badges = sum(len(BADGE.findall(text)) for relative, text in pages.items() if is_summary_page(relative))
    return f"issue tag links: {chips} panel chips and {badges} summary badges linked, {changed} files rewritten"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--site-dir", required=True, type=Path, help="the rendered html-multi directory")
    parser.add_argument("--repository", required=True, help="GitHub repository as owner/name")
    args = parser.parse_args(argv)
    try:
        print(run(args.site_dir, args.repository))
    except UsageError as error:
        parser.exit(2, f"{parser.prog}: error: {error}\n")
    except ValidationError as error:
        print(f"{parser.prog}: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
