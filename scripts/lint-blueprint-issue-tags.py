#!/usr/bin/env python3
"""Check the GitHub issue tags on blueprint nodes.

A `definition`/`theorem` block under `docs/SecureMessagingDocs/Chapters/` links
the GitHub issue tracking its formalization with `(tags := "gh-<n>")` on its
opening directive. verso-blueprint carries the tag into `blueprint-manifest.json`,
where the coverage scripts and downstream tooling read it, and
`link-blueprint-issue-tags.py` turns the rendered chip into a link after the
render. verso-blueprint itself only trims,
lowercases and dedupes tags, so this lint enforces the contract:

- every tag starting with `gh-` matches `^gh-[1-9][0-9]*$`, written in lowercase
  (the source must spell what the manifest carries);
- no two tag tokens normalize to the same value, an opener has at most one
  `tags` option, and its value is one double-quoted string (anything else is
  reported rather than treated as "no tags");
- issue tags appear only on `definition`/`theorem` directives (verso-blueprint
  rejects `tags` on proof blocks; other directives are not tracked atoms);
- the retired `{githubIssue N}` / `{githubLabel}` footer roles do not appear.

Supported syntax is deliberately restricted: unindented colon-run openers
(`:{3,}kind "label" (opts…)`), continued onto following lines while parentheses
outside quoted values are unbalanced, never past a closer or another opener; closers are colon-only lines matching the opener; fences are
backtick runs of three or more, closed by a run at least as long; `tags` values
are double-quoted with no escaped quotes or newlines. Anything outside the
subset is an error, not silently accepted. Only chapter files are scanned; they
are Verso markup, so Lean comments and strings do not occur outside fences.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

DEFAULT_CHAPTERS = Path("docs/SecureMessagingDocs/Chapters")
STATEMENT_KINDS = ("definition", "theorem")

ANY_OPEN = re.compile(r"^(:{3,})\s*(\w+)(.*)$")
LABEL = re.compile(r'^\s*"([^"\\]+)"')
INDENTED_OPEN = re.compile(r"^\s+:{3,}\s*\w+")
FENCE = re.compile(r"^\s*(`{3,})")
TAGS_OPT = re.compile(r'\(tags\s*:=\s*"([^"\\\r\n]*)"\)')  # no escapes, no line breaks
TAGS_ANY = re.compile(r"\btags\s*:=")  # every tags option, well-formed or not
GH_TAG = re.compile(r"^gh-([1-9][0-9]*)$")
LEGACY_FOOTER = re.compile(r"githubIssue|githubLabel")
QUOTED = re.compile(r'"(?:[^"\\]|\\.)*"', re.DOTALL)  # a complete double-quoted value, escapes and line breaks allowed


def paren_depth(text: str) -> int:
    # Unclosed `(` outside quoted values: a `(` inside a title must not start a continuation.
    unquoted = QUOTED.sub('""', text)
    return unquoted.count("(") - unquoted.count(")")


def ends_opener(line: str) -> bool:
    # A closer or another opener can never be part of the current opener.
    return re.fullmatch(r":{3,}", line.strip()) is not None or ANY_OPEN.match(line) is not None


@dataclass
class Block:
    path: Path
    start: int  # 0-based index of the opener's first line
    colons: str
    kind: str
    label: str | None
    tags_options: list[str]  # raw values of every well-formed (tags := "...") on the opener
    malformed_tags: int = 0  # `tags :=` occurrences the well-formed pattern did not match
    legacy: list[tuple[int, str]] = field(default_factory=list)  # (line, retired role found there)

    def tag_tokens(self) -> list[str]:
        return [t.strip() for v in self.tags_options for t in v.split(",") if t.strip()]


@dataclass
class Diag:
    path: Path
    line: int  # 1-based, 0 for whole-file
    msg: str

    def __str__(self) -> str:
        return f"{self.path}:{self.line}: {self.msg}"


def scan_blocks(path: Path, lines: list[str]) -> tuple[list[Block], list[Diag]]:
    """Return (closed blocks, structural diagnostics). Never exits."""
    blocks: list[Block] = []
    diags: list[Diag] = []
    stack: list[Block] = []
    fence: str | None = None
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if fence:
            if re.fullmatch(r"`{%d,}" % len(fence), stripped):
                fence = None
            i += 1
            continue
        fm = FENCE.match(line)
        if fm:
            fence = fm.group(1)
            i += 1
            continue
        if INDENTED_OPEN.match(line):
            diags.append(Diag(path, i + 1, "indented directive opener"))
            i += 1
            continue
        m = ANY_OPEN.match(line)
        if m:
            rest, j = m.group(3), i
            # An opener continues onto following lines until its parentheses balance
            # (e.g. a long `lean := "..."` list). Parentheses inside quoted values do
            # not count, and a closer or another opener always ends the continuation.
            while paren_depth(rest) > 0 and j + 1 < len(lines) and not ends_opener(lines[j + 1]):
                j += 1
                rest += "\n" + lines[j]
            if paren_depth(rest) != 0:
                diags.append(Diag(path, i + 1, "directive opener has unbalanced parentheses"))
            lm = LABEL.match(rest)
            tags = TAGS_OPT.findall(rest)
            stack.append(
                Block(path, i, m.group(1), m.group(2), lm.group(1) if lm else None, tags, len(TAGS_ANY.findall(rest)) - len(tags))
            )
            i = j + 1
            continue
        if re.fullmatch(r":{3,}", stripped):
            if not stack or stripped != stack[-1].colons:
                diags.append(Diag(path, i + 1, f"closer {stripped} does not match innermost directive"))
            else:
                blocks.append(stack.pop())
            i += 1
            continue
        lf = LEGACY_FOOTER.search(line)
        if lf:
            if stack:
                stack[-1].legacy.append((i, lf.group(0)))
            else:
                diags.append(Diag(path, i + 1, f"retired {lf.group(0)} footer role outside any directive"))
        i += 1
    if fence:
        diags.append(Diag(path, 0, "code fence open at end of file"))
    for b in stack:
        diags.append(Diag(path, b.start + 1, f"unclosed directive {b.kind}"))
    blocks.sort(key=lambda b: b.start)
    return blocks, diags


def lint_block(b: Block) -> list[Diag]:
    diags: list[Diag] = []
    opener_line = b.start + 1
    who = b.label or b.kind
    if b.malformed_tags:
        diags.append(Diag(b.path, opener_line, f'{who}: malformed (tags := ...) option; the value must be one double-quoted string'))
    if len(b.tags_options) > 1:
        diags.append(Diag(b.path, opener_line, f"{who}: more than one (tags := ...) option"))
    seen: set[str] = set()
    has_issue_tag = False
    for tok in b.tag_tokens():
        norm = tok.lower()
        if norm in seen:
            diags.append(Diag(b.path, opener_line, f"{who}: duplicate tag {tok!r}"))
        seen.add(norm)
        if norm.startswith("gh-"):
            has_issue_tag = True
            if GH_TAG.match(tok) is None:
                diags.append(
                    Diag(b.path, opener_line, f"{who}: tag {tok!r} is not a valid issue tag; expected gh-<n>, lowercase, no leading zero")
                )
    if has_issue_tag and (b.kind not in STATEMENT_KINDS or b.label is None):
        diags.append(Diag(b.path, opener_line, f"issue tags on a `{b.kind}` block; they belong on the definition/theorem directive"))
    for line, role in b.legacy:
        diags.append(
            Diag(b.path, line + 1, f'{who}: the {role} footer role was retired; write (tags := "gh-<n>") on the statement directive')
        )
    return diags


def lint(chapters: Path = DEFAULT_CHAPTERS) -> list[Diag]:
    paths = sorted(chapters.rglob("*.lean"))
    if not paths:
        return [Diag(chapters, 0, "no chapter files found")]
    diags: list[Diag] = []
    for path in paths:
        blocks, scan_diags = scan_blocks(path, path.read_text().splitlines())
        diags.extend(scan_diags)
        for b in blocks:
            diags.extend(lint_block(b))
    return diags


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--chapters", type=Path, default=DEFAULT_CHAPTERS)
    args = parser.parse_args()
    diags = lint(args.chapters)
    for d in diags:
        print(d, file=sys.stderr)
    if diags:
        print(f"{len(diags)} blueprint issue tag error(s)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
