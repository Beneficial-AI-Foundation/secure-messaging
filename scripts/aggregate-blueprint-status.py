#!/usr/bin/env python3
"""Summarize Blueprint atom coverage from a rendered split Verso site.

Each chapter render emits a Blueprint preview manifest. This script reads those
manifests, counts definition/theorem atoms, and reports whether each atom has an
associated Lean block and appears fully verified.
"""

import argparse
import html as html_module
import json
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


DEFAULT_SITE_DIR = Path("_out/site/html-multi")
MANIFEST_PATH = "-verso-data/blueprint-preview-manifest.json"
TRACKED_KINDS = ("definition", "theorem")


@dataclass(frozen=True)
class Atom:
    kind: str
    label: str
    title: str
    chapter: str
    href: str
    specified: bool
    verified: bool


def chapter_name(manifest: Path, site_dir: Path) -> str:
    try:
        return manifest.relative_to(site_dir).parts[0]
    except ValueError:
        return manifest.parent.parent.name


def strip_tags(html: str) -> str:
    return re.sub(r"<[^>]*>", " ", html)


def classify(entry: dict, chapter: str) -> Atom:
    html = entry.get("html", "")
    text = strip_tags(html).lower()

    # The rendered preview HTML is the only status source available here. The
    # Lean pill renderer marks missing/partial declarations, while any remaining
    # `sorry` text means the statement is specified but not fully verified.
    specified = 'class="hl lean block"' in html
    has_missing_marker = 'data-status="missing"' in html
    has_partial_marker = 'data-status="partial"' in html
    has_sorry = "sorry" in text
    verified = specified and not has_missing_marker and not has_partial_marker and not has_sorry
    return Atom(
        kind=entry.get("kind", ""),
        label=entry.get("label", ""),
        title=entry.get("title", ""),
        chapter=chapter,
        href=entry.get("href", ""),
        specified=specified,
        verified=verified,
    )


def load_atoms(site_dir: Path) -> list[Atom]:
    # The split site stores one manifest per chapter under
    # <chapter>/-verso-data/blueprint-preview-manifest.json.
    manifests = sorted(site_dir.glob(f"*/{MANIFEST_PATH}"))
    if not manifests:
        raise SystemExit(
            f"No blueprint preview manifests found under {site_dir}. "
            "Run scripts/render-docs-site.sh first."
        )

    atoms: list[Atom] = []
    seen_labels: set[str] = set()
    duplicates: set[str] = set()
    for manifest in manifests:
        chapter = chapter_name(manifest, site_dir)
        data = json.loads(manifest.read_text())
        for entry in data.get("previews", []):
            if entry.get("splitPreviewCopy"):
                continue
            if entry.get("targetKind") != "block" or entry.get("kind") not in TRACKED_KINDS:
                continue
            atom = classify(entry, chapter)
            if atom.label in seen_labels:
                duplicates.add(atom.label)
            seen_labels.add(atom.label)
            atoms.append(atom)

    if duplicates:
        duplicate_list = ", ".join(sorted(duplicates))
        raise SystemExit(f"Duplicate blueprint labels found: {duplicate_list}")

    return atoms


def summarize(atoms: list[Atom]) -> dict[str, Counter]:
    totals: dict[str, Counter] = {kind: Counter() for kind in TRACKED_KINDS}
    for atom in atoms:
        totals[atom.kind]["total"] += 1
        totals[atom.kind]["specified"] += int(atom.specified)
        totals[atom.kind]["verified"] += int(atom.verified)
    return totals


def summarize_by_chapter(atoms: list[Atom]) -> dict[str, dict[str, Counter]]:
    chapters: dict[str, dict[str, Counter]] = defaultdict(lambda: {kind: Counter() for kind in TRACKED_KINDS})
    for atom in atoms:
        counter = chapters[atom.chapter][atom.kind]
        counter["total"] += 1
        counter["specified"] += int(atom.specified)
        counter["verified"] += int(atom.verified)
    return chapters


def print_counter(name: str, counter: Counter) -> None:
    print(name)
    print(f"  Total:     {counter['total']}")
    print(f"  Specified: {counter['specified']}")
    print(f"  Verified:  {counter['verified']}")


def print_text_report(atoms: list[Atom], by_chapter: bool) -> None:
    totals = summarize(atoms)
    print("Blueprint Status")
    print_counter("Definitions", totals["definition"])
    print_counter("Theorems", totals["theorem"])

    if not by_chapter:
        return

    print("By Chapter")
    for chapter, chapter_totals in sorted(summarize_by_chapter(atoms).items()):
        definition = chapter_totals["definition"]
        theorem = chapter_totals["theorem"]
        print(
            f"  {chapter}: "
            f"definitions {definition['total']}/{definition['specified']}/{definition['verified']}, "
            f"theorems {theorem['total']}/{theorem['specified']}/{theorem['verified']}"
        )


def atoms_for(atoms: list[Atom], chapter: str, kind: str, metric: str) -> list[Atom]:
    chapter_atoms = [atom for atom in atoms if atom.chapter == chapter and atom.kind == kind]
    if metric == "total":
        return chapter_atoms
    if metric == "specified":
        return [atom for atom in chapter_atoms if atom.specified]
    if metric == "verified":
        return [atom for atom in chapter_atoms if atom.verified]
    raise ValueError(f"unknown metric: {metric}")


def status_count_cell(chapter: str, kind: str, metric: str, atoms: list[Atom], extra_class: str = "") -> str:
    count = len(atoms)
    class_attr = f' class="{extra_class}"' if extra_class else ""
    chapter_text = html_module.escape(chapter.replace("-", " "))
    metric_text = html_module.escape(metric.title())
    kind_text = html_module.escape(kind.title())
    atom_items = []

    # Counts in the table are focusable; the popover gives reviewers a quick path
    # from each aggregate number to the atoms that make it up.
    for atom in sorted(atoms, key=lambda item: item.label):
        label = html_module.escape(atom.label)
        title = html_module.escape(atom.title)
        href = html_module.escape(f"{chapter}/{atom.href}", quote=True)
        detail = f" <span>{title}</span>" if title else ""
        atom_items.append(f'<li><a href="{href}"><code>{label}</code></a>{detail}</li>')
    if not atom_items:
        atom_items.append("<li>No atoms</li>")
    atom_list = "".join(atom_items)
    label = f"{metric_text} {kind_text} atoms for {chapter_text}"
    return (
        f'<td{class_attr}><span class="status-count" tabindex="0" aria-label="{label}">'
        f'<span class="status-number">{count}</span>'
        f'<span class="status-popover" role="tooltip"><strong>{label}</strong><ul>{atom_list}</ul></span>'
        "</span></td>"
    )


def print_html_summary(atoms: list[Atom]) -> None:
    totals = summarize(atoms)
    chapters = summarize_by_chapter(atoms)
    print('    <section class="blueprint-status" aria-labelledby="blueprint-status-heading">')
    print('      <h2 id="blueprint-status-heading">Blueprint Status</h2>')
    print('      <div class="status-summary">')
    for label, kind in (("Definitions", "definition"), ("Theorems", "theorem")):
        counter = totals[kind]
        total = counter["total"]
        specified = counter["specified"]
        verified = counter["verified"]
        print('        <div class="status-card">')
        print(f'          <h3>{label}</h3>')
        print('          <dl>')
        print(f'            <div><dt>Total</dt><dd>{total}</dd></div>')
        print(f'            <div><dt>Specified</dt><dd>{specified}</dd></div>')
        print(f'            <div><dt>Verified</dt><dd>{verified}</dd></div>')
        print('          </dl>')
        print('        </div>')
    print('      </div>')
    print('      <table class="status-table">')
    print('        <caption>Per-chapter blueprint status</caption>')
    print('        <thead>')
    print('          <tr><th scope="col" rowspan="2">Chapter</th><th scope="colgroup" colspan="3">Definitions</th><th class="theorem-group" scope="colgroup" colspan="3">Theorems</th></tr>')
    print('          <tr><th scope="col">Total</th><th scope="col">Specified</th><th scope="col">Verified</th><th class="theorem-group" scope="col">Total</th><th scope="col">Specified</th><th scope="col">Verified</th></tr>')
    print('        </thead>')
    print('        <tbody>')
    for chapter, chapter_totals in sorted(chapters.items()):
        chapter_text = html_module.escape(chapter.replace("-", " "))
        definition_total = atoms_for(atoms, chapter, "definition", "total")
        definition_specified = atoms_for(atoms, chapter, "definition", "specified")
        definition_verified = atoms_for(atoms, chapter, "definition", "verified")
        theorem_total = atoms_for(atoms, chapter, "theorem", "total")
        theorem_specified = atoms_for(atoms, chapter, "theorem", "specified")
        theorem_verified = atoms_for(atoms, chapter, "theorem", "verified")
        cells = "".join(
            [
                status_count_cell(chapter, "definition", "total", definition_total),
                status_count_cell(chapter, "definition", "specified", definition_specified),
                status_count_cell(chapter, "definition", "verified", definition_verified),
                status_count_cell(chapter, "theorem", "total", theorem_total, "theorem-group"),
                status_count_cell(chapter, "theorem", "specified", theorem_specified),
                status_count_cell(chapter, "theorem", "verified", theorem_verified),
            ]
        )
        print(f'          <tr><th scope="row">{chapter_text}</th>{cells}</tr>')
    print('        </tbody>')
    print('      </table>')
    print('    </section>')


def json_report(atoms: list[Atom]) -> dict:
    totals = summarize(atoms)
    chapters = summarize_by_chapter(atoms)
    return {
        "summary": {
            kind: {
                "total": totals[kind]["total"],
                "specified": totals[kind]["specified"],
                "verified": totals[kind]["verified"],
                "missing": totals[kind]["total"] - totals[kind]["specified"],
                "unproved": totals[kind]["specified"] - totals[kind]["verified"],
            }
            for kind in TRACKED_KINDS
        },
        "chapters": {
            chapter: {
                kind: {
                    "total": chapter_totals[kind]["total"],
                    "specified": chapter_totals[kind]["specified"],
                    "verified": chapter_totals[kind]["verified"],
                }
                for kind in TRACKED_KINDS
            }
            for chapter, chapter_totals in sorted(chapters.items())
        },
        "atoms": [atom.__dict__ for atom in atoms],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Aggregate Verso blueprint atom status from rendered chapter manifests.")
    parser.add_argument("--site-dir", type=Path, default=DEFAULT_SITE_DIR)
    parser.add_argument("--by-chapter", action="store_true")
    parser.add_argument("--html-summary", action="store_true")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args()

    atoms = load_atoms(args.site_dir)
    if args.html_summary:
        print_html_summary(atoms)
    elif args.as_json:
        print(json.dumps(json_report(atoms), indent=2, sort_keys=True))
    else:
        print_text_report(atoms, args.by_chapter)


if __name__ == "__main__":
    main()