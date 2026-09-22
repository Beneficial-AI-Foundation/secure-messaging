#!/usr/bin/env python3
"""Remove redundant fragments pointing to a rendered page's top-level section.

Doing this in the generated HTML avoids both the browser's initial fragment jump
and the later disclosure-reveal scroll. Anchors within a page remain intact.
"""

import argparse
from html import escape
from html.parser import HTMLParser
from pathlib import Path
import re
from urllib.parse import unquote, urljoin, urlsplit, urlunsplit


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.line_offsets = [0]
        for line in text.splitlines(keepends=True):
            self.line_offsets.append(self.line_offsets[-1] + len(line))
        self.base = ''
        self.in_main = False
        self.section_depth = 0
        self.sections = []
        self.links = []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'base':
            self.base = attrs.get('href', '')
        if tag == 'a' and 'href' in attrs:
            line, column = self.getpos()
            self.links.append((self.get_starttag_text(), attrs['href'],
                               self.line_offsets[line - 1] + column))
        if tag == 'main':
            self.in_main = True
        if self.in_main and tag == 'section':
            self.section_depth += 1
            if self.section_depth == 1:
                self.sections.append([attrs.get('id'), False])
        if self.in_main and tag == 'h1' and self.section_depth == 1:
            self.sections[-1][1] = True

    def handle_endtag(self, tag):
        if self.in_main and tag == 'section':
            self.section_depth -= 1
        if tag == 'main':
            self.in_main = False


def normalize(site):
    origin = 'https://rendered.invalid/'
    pages = {}
    targets = {}
    for path in site.rglob('*.html'):
        text = path.read_text()
        page = Page(text)
        url = urljoin(origin, path.relative_to(site).as_posix())
        pages[path] = (text, page, url)
        if len(page.sections) == 1:
            identifier, has_heading = page.sections[0]
            if identifier and has_heading:
                targets[url] = identifier
                if url.endswith('/index.html'):
                    targets[url[:-len('index.html')]] = identifier
    changed = 0
    for path, (text, page, url) in pages.items():
        base = urljoin(url, page.base)
        for tag, href, offset in reversed(page.links):
            destination = urlsplit(urljoin(base, href))
            key = urlunsplit(destination._replace(query='', fragment=''))
            if not destination.fragment or targets.get(key) != unquote(destination.fragment):
                continue
            # Keep fragment-only links: they can reset a currently scrolled page.
            if not urlsplit(href).path:
                continue
            replacement = href.split('#', 1)[0]
            new_tag = re.sub(r'''(\s+href\s*=\s*)(["'])(.*?)\2''',
                             lambda m: m[1] + m[2] + escape(replacement, quote=True) + m[2],
                             tag, count=1, flags=re.IGNORECASE | re.DOTALL)
            text = text[:offset] + new_tag + text[offset + len(tag):]
        if text != pages[path][0]:
            path.write_text(text)
            changed += 1
    return changed


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site-dir', type=Path, required=True)
    args = parser.parse_args()
    print(f'Section navigation: normalized {normalize(args.site_dir)} pages')
