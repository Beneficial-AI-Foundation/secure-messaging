#!/usr/bin/env python3
"""Remove the redundant fragment from links to a chapter's own top heading.

Verso writes chapter links as ``Chapter/#chapter-heading``. Since that heading
is already at the top of the destination page, the fragment makes the browser
scroll once while loading and again after the page initializes. This script
rewrites those links to ``Chapter/`` in the rendered site. Links to anything
inside a page, such as a Lean declaration or nested section, keep their anchor.
"""

import argparse
from pathlib import Path
import re
from urllib.parse import unquote, urljoin, urlsplit, urlunsplit


CHAPTER = re.compile(r'<main\b.*?<section\s+id="([^"]+)"\s*>\s*<h1\b', re.DOTALL)
HREF = re.compile(r'(?P<prefix><a\b[^>]*\bhref=")(?P<href>[^"]+)(?P<suffix>")')
ORIGIN = "https://rendered.invalid/"


def chapter_targets(site_dir: Path) -> dict[str, str]:
    """Map each rendered chapter URL to the id of its top heading."""
    targets = {}
    for page in site_dir.rglob("*.html"):
        match = CHAPTER.search(page.read_text())
        if not match:
            continue
        url = urljoin(ORIGIN, page.relative_to(site_dir).as_posix())
        targets[url] = match[1]
        if url.endswith("/index.html"):
            targets[url[:-len("index.html")]] = match[1]
    return targets


def normalize(site_dir: Path) -> int:
    targets = chapter_targets(site_dir)
    changed = 0
    for page in site_dir.rglob("*.html"):
        text = page.read_text()
        page_url = urljoin(ORIGIN, page.relative_to(site_dir).as_posix())

        def rewrite(match: re.Match[str]) -> str:
            href = match["href"]
            target = urlsplit(urljoin(page_url, href))
            target_url = urlunsplit(target._replace(query="", fragment=""))
            # An empty path is a same-page link and should remain an anchor.
            if not urlsplit(href).path or targets.get(target_url) != unquote(target.fragment):
                return match[0]
            return match["prefix"] + href.split("#", 1)[0] + match["suffix"]

        rewritten = HREF.sub(rewrite, text)
        if rewritten != text:
            page.write_text(rewritten)
            changed += 1
    return changed


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site-dir", type=Path, required=True)
    args = parser.parse_args()
    print(f"Section navigation: normalized {normalize(args.site_dir)} pages")
