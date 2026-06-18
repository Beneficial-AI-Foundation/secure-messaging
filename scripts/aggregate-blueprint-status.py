#!/usr/bin/env python3
"""Summarize Blueprint atom coverage from a rendered split Verso site.

Each chapter render emits a Blueprint preview manifest. This script reads those
manifests and counts definition/theorem atoms. Definitions are specified only
when they have a complete Lean block, while theorems separately track whether a
Lean statement exists and whether it appears fully verified.
"""

import argparse
from datetime import datetime, timedelta, timezone
import html as html_module
import json
import posixpath
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


DEFAULT_SITE_DIR = Path("_out/site/html-multi")
DEFAULT_DOCS_DIR = Path("docs/SecureMessagingDocs")
DEFAULT_PROJECT_END = "2027-01-28"
MANIFEST_PATH = "-verso-data/blueprint-preview-manifest.json"
TRACKED_KINDS = ("definition", "theorem")
ATOM_RE = re.compile(r":{3,}(definition|theorem)\s+\"([^\"]+)\"")
ISSUE_RE = re.compile(r"\{githubIssue\s+(\d+)\}")
CHART_WIDTH = 1153
CHART_HEIGHT = 546
CHART_PADDING_LEFT = 37
CHART_PADDING_RIGHT = 44
CHART_PADDING_TOP = 42
CHART_PADDING_BOTTOM = 132
CHART_TICK_LABEL_X = -8
CHART_TICK_LABEL_Y = 30
CHAPTER_TITLES = {
    "Authenticated-Encryption-with-Associated-Data": "Authenticated Encryption with Associated Data",
    "Continuous-Key-Agreement": "Continuous Key Agreement",
    "Erasure-Codes": "Erasure Codes",
    "Forward-Secure-AEAD": "Forward-Secure AEAD",
    "Online-Offline-KEM": "Online-Offline KEM",
    "PRF-PRNG": "PRF-PRNG",
    "Ratcheting-KEM": "Ratcheting KEM",
    "Sparse-Continuous-Key-Agreement": "Sparse Continuous Key Agreement",
    "Secure-Messaging": "Secure Messaging",
}
CHAPTER_ORDER = tuple(CHAPTER_TITLES)


@dataclass(frozen=True)
class ChartWindow:
    start: datetime | None
    end: datetime | None


@dataclass(frozen=True)
class Atom:
    kind: str
    label: str
    title: str
    chapter: str
    href: str
    specified: bool
    verified: bool


@dataclass(frozen=True)
class ReadyNextItem:
    chapter: str
    label: str
    href: str


def chapter_name(manifest: Path, site_dir: Path) -> str:
    # Derive the chapter slug that owns a preview manifest.
    try:
        return manifest.relative_to(site_dir).parts[0]
    except ValueError:
        return manifest.parent.parent.name


def chapter_title(chapter: str) -> str:
    # Match the display titles used by the generated root chapter index.
    return CHAPTER_TITLES.get(chapter, chapter.replace("-", " "))


def chapter_sort_key(chapter: str) -> tuple[int, str]:
    # Match the explicit chapter order used by the generated root chapter index.
    try:
        return (CHAPTER_ORDER.index(chapter), "")
    except ValueError:
        return (len(CHAPTER_ORDER), chapter_title(chapter))


def strip_tags(html: str) -> str:
    # Remove HTML tags while preserving rough word boundaries.
    return re.sub(r"<[^>]*>", " ", html)


def compact_text(html: str) -> str:
    # Convert small HTML fragments into normalized display text.
    return html_module.unescape(re.sub(r"\s+", " ", strip_tags(html)).strip())


def classify(entry: dict, chapter: str) -> Atom:
    # Convert one preview manifest entry into an Atom status record.
    html = entry.get("html", "")
    text = strip_tags(html).lower()

    # The rendered preview HTML is the only status source available here. The
    # Lean pill renderer marks missing/partial declarations, while any remaining
    # `sorry` text means the Lean side is incomplete.
    has_lean_block = 'class="hl lean block"' in html
    has_missing_marker = 'data-status="missing"' in html
    has_partial_marker = 'data-status="partial"' in html
    has_sorry = "sorry" in text
    verified = has_lean_block and not has_missing_marker and not has_partial_marker and not has_sorry
    specified = verified if entry.get("kind", "") == "definition" else has_lean_block
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
    # Load all non-copy Blueprint atoms from the split site's chapter manifests.
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


def load_tracked_labels(docs_dir: Path) -> set[str]:
    # Track only authored Blueprint atoms that carry a GitHub issue footer.
    labels: set[str] = set()
    for path in sorted(docs_dir.rglob("*.lean")):
        lines = path.read_text().splitlines()
        index = 0
        while index < len(lines):
            match = ATOM_RE.search(lines[index])
            if match is None:
                index += 1
                continue

            label = match.group(2)
            fence = re.match(r"\s*(:{3,})", lines[index])
            close_marker = fence.group(1) if fence is not None else ":::"
            block = [lines[index]]
            index += 1
            while index < len(lines):
                block.append(lines[index])
                if lines[index].strip() == close_marker:
                    index += 1
                    break
                index += 1

            if ISSUE_RE.search("\n".join(block)):
                labels.add(label)
    return labels


def load_tracked_atoms(site_dir: Path, docs_dir: Path = DEFAULT_DOCS_DIR) -> list[Atom]:
    # Filter rendered atoms to the one-to-one tracked issue set.
    tracked = load_tracked_labels(docs_dir)
    return [atom for atom in load_atoms(site_dir) if atom.label in tracked]


def normalize_chapter_href(chapter: str, href: str) -> str:
    # Make Blueprint-Summary links usable from the root index page.
    if href.startswith(("http://", "https://", "#")):
        return href
    return posixpath.normpath(f"{chapter}/Blueprint-Summary/{href}")


def extract_ready_next_items(summary_html: str, chapter: str) -> list[ReadyNextItem]:
    # Extract atoms listed in a chapter's Ready next summary section.
    return extract_summary_section_items(summary_html, chapter, "Ready next")


def extract_current_blocker_items(summary_html: str, chapter: str) -> list[ReadyNextItem]:
    # Extract atoms listed in a chapter's Current blockers summary section.
    return extract_summary_section_items(summary_html, chapter, "Current blockers")


def extract_summary_section_items(summary_html: str, chapter: str, section_title: str) -> list[ReadyNextItem]:
    # Parse one named disclosure section from a rendered Blueprint summary page.
    title_pattern = re.escape(section_title)
    match = re.search(
        rf'<details[^>]*class="[^"]*bp_summary_subsection[^"]*"[^>]*>\s*<summary>\s*{title_pattern}\s*\([^)]*\)\s*</summary>(.*?)</details>',
        summary_html,
        flags=re.IGNORECASE | re.DOTALL,
    )
    if not match:
        return []

    items: list[ReadyNextItem] = []
    for li_html in re.findall(r"<li\b[^>]*>(.*?)</li>", match.group(1), flags=re.IGNORECASE | re.DOTALL):
        anchor = re.search(r'<a[^>]*href="([^"]+)"[^>]*>(.*?)</a>', li_html, flags=re.IGNORECASE | re.DOTALL)
        if anchor is None:
            continue
        href = normalize_chapter_href(chapter, anchor.group(1).strip())
        label = compact_text(anchor.group(2))
        items.append(ReadyNextItem(chapter=chapter, label=label, href=href))
    return items


def load_ready_next_by_chapter(site_dir: Path) -> dict[str, list[ReadyNextItem]]:
    # Load Ready next items from every chapter summary page.
    ready_by_chapter: dict[str, list[ReadyNextItem]] = {}
    for summary_file in sorted(site_dir.glob("*/Blueprint-Summary/index.html")):
        chapter = summary_file.parts[-3]
        items = extract_ready_next_items(summary_file.read_text(), chapter)
        if items:
            ready_by_chapter[chapter] = items
    return ready_by_chapter


def load_current_blockers_by_chapter(site_dir: Path) -> dict[str, list[ReadyNextItem]]:
    # Load Current blockers items from every chapter summary page.
    blockers_by_chapter: dict[str, list[ReadyNextItem]] = {}
    for summary_file in sorted(site_dir.glob("*/Blueprint-Summary/index.html")):
        chapter = summary_file.parts[-3]
        items = extract_current_blocker_items(summary_file.read_text(), chapter)
        if items:
            blockers_by_chapter[chapter] = items
    return blockers_by_chapter


def summarize(atoms: list[Atom]) -> dict[str, Counter]:
    # Count total/specified/verified atoms across the whole site.
    totals: dict[str, Counter] = {kind: Counter() for kind in TRACKED_KINDS}
    for atom in atoms:
        totals[atom.kind]["total"] += 1
        totals[atom.kind]["specified"] += int(atom.specified)
        totals[atom.kind]["verified"] += int(atom.verified)
    return totals


def summarize_by_chapter(atoms: list[Atom]) -> dict[str, dict[str, Counter]]:
    # Count total/specified/verified atoms separately for each chapter.
    chapters: dict[str, dict[str, Counter]] = defaultdict(lambda: {kind: Counter() for kind in TRACKED_KINDS})
    for atom in atoms:
        counter = chapters[atom.chapter][atom.kind]
        counter["total"] += 1
        counter["specified"] += int(atom.specified)
        counter["verified"] += int(atom.verified)
    return chapters


def print_counter(name: str, counter: Counter, show_verified: bool = True) -> None:
    # Print one text-report counter block.
    print(name)
    print(f"  Total:     {counter['total']}")
    print(f"  Specified: {counter['specified']}")
    if show_verified:
        print(f"  Verified:  {counter['verified']}")


def print_text_report(atoms: list[Atom], by_chapter: bool) -> None:
    # Print the command-line text report.
    totals = summarize(atoms)
    print("Blueprint Status")
    print_counter("Definitions", totals["definition"], show_verified=False)
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
    # Select atoms for one chapter/kind/metric table cell.
    chapter_atoms = [atom for atom in atoms if atom.chapter == chapter and atom.kind == kind]
    if metric == "total":
        return chapter_atoms
    if metric == "specified":
        return [atom for atom in chapter_atoms if atom.specified]
    if metric == "verified":
        return [atom for atom in chapter_atoms if atom.verified]
    raise ValueError(f"unknown metric: {metric}")


def status_count_cell(
    chapter: str,
    kind: str,
    metric: str,
    atoms: list[Atom],
    extra_class: str = "",
) -> str:
    # Render one status-table cell with a count and atom popover.
    count = len(atoms)
    class_attr = f' class="{extra_class}"' if extra_class else ""
    chapter_text = html_module.escape(chapter_title(chapter))
    metric_text = html_module.escape(metric.capitalize())
    kind_text = html_module.escape(kind)
    atom_items = []

    # Counts in the table are focusable; the popover gives reviewers a quick path
    # from each aggregate number to the atoms that make it up.
    for atom in sorted(atoms, key=lambda item: item.label):
        label = html_module.escape(atom.label)
        title = html_module.escape(atom.title)
        href_chapter = atom.chapter if chapter == "ALL" else chapter
        href = html_module.escape(f"{href_chapter}/{atom.href}", quote=True)
        detail = f" <span>{title}</span>" if title else ""
        atom_items.append(f'<li><a href="{href}"><code>{label}</code></a>{detail}</li>')
    if not atom_items:
        atom_items.append("<li>No atoms</li>")
    atom_list = "".join(atom_items)
    label = f"{metric_text} {kind_text} atoms for {chapter_text}"
    return (
        f'<td{class_attr}><span class="status-count" tabindex="0" aria-label="{label}">'
        f'<span class="status-number">{count}</span>'
        f'<span class="status-popover" role="tooltip"><ul>{atom_list}</ul></span>'
        "</span></td>"
    )


def load_history_document(path: Path | None) -> dict:
    # Load a complete history document, or an empty document when absent.
    if path is None or not path.exists():
        return {"snapshots": []}
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return {"snapshots": []}
    # Accept a bare snapshot list as a minimal history document.
    if isinstance(data, list):
        return {"snapshots": data}
    return data if isinstance(data, dict) else {"snapshots": []}


def snapshot_time(snapshot: dict) -> datetime | None:
    # Parse a snapshot's date field for sorting and chart placement.
    raw_date = snapshot.get("date")
    if not isinstance(raw_date, str) or not raw_date:
        return None
    try:
        parsed = datetime.fromisoformat(raw_date.replace("Z", "+00:00"))
        return parsed if parsed.tzinfo is not None else parsed.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def parse_datetime(raw_date: object) -> datetime | None:
    # Parse optional ISO timestamps from history metadata.
    if not isinstance(raw_date, str) or not raw_date:
        return None
    try:
        parsed = datetime.fromisoformat(raw_date.replace("Z", "+00:00"))
        return parsed if parsed.tzinfo is not None else parsed.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def sorted_history(path: Path | None) -> list[dict]:
    # Return history snapshots sorted by parsed timestamp.
    snapshots = load_history_document(path).get("snapshots", [])
    return sorted(snapshots, key=lambda snapshot: snapshot_time(snapshot) or datetime.min.replace(tzinfo=timezone.utc))


def chart_window(history: dict, snapshots: list[dict]) -> ChartWindow:
    # Resolve the chart time window from history metadata or snapshots.
    start = parse_datetime(history.get("projectStart"))
    if start is None and snapshots:
        start = snapshot_time(snapshots[0])
    end = parse_datetime(history.get("projectEnd")) or parse_datetime(DEFAULT_PROJECT_END)
    return ChartWindow(start=start, end=end)


def metric_value(snapshot: dict, kind: str, metric: str) -> int:
    # Read one integer metric from a history snapshot.
    value = snapshot.get(kind, {}).get(metric, 0)
    return value if isinstance(value, int) else 0


def chart_coordinates(
    snapshots: list[dict],
    kind: str,
    metric: str,
    max_value: int,
    window: ChartWindow,
) -> list[tuple[float, float]]:
    # Map history metric values into SVG coordinates.
    if not snapshots:
        return []

    times = [snapshot_time(snapshot) for snapshot in snapshots]
    dated = [time for time in times if time is not None]
    first = window.start or (min(dated) if dated else None)
    last = window.end or (max(dated) if dated else None)
    span = (last - first).total_seconds() if first is not None and last is not None else 0
    plot_width = CHART_WIDTH - CHART_PADDING_LEFT - CHART_PADDING_RIGHT
    plot_height = CHART_HEIGHT - CHART_PADDING_TOP - CHART_PADDING_BOTTOM

    coordinates = []
    for index, snapshot in enumerate(snapshots):
        time = times[index]
        if first is not None and time is not None and span > 0:
            position = (time - first).total_seconds() / span
            x = CHART_PADDING_LEFT + plot_width * min(max(position, 0), 1)
        elif len(snapshots) > 1:
            x = CHART_PADDING_LEFT + plot_width * (index / (len(snapshots) - 1))
        else:
            x = CHART_PADDING_LEFT + plot_width
        value = metric_value(snapshot, kind, metric)
        y = CHART_PADDING_TOP + plot_height * (1 - (value / max_value if max_value else 0))
        coordinates.append((x, y))
    return coordinates


def chart_max_value(raw_max: int) -> int:
    # Round up to the next five-atom tick so the top line has visual headroom.
    return max(5, ((raw_max + 4) // 5) * 5)


def displayed_points(points: list[tuple[float, float]], full_width: bool = False) -> list[tuple[float, float]]:
    # Extend sparse point sets so SVG lines and areas remain visible.
    if full_width and points:
        extended = list(points)
        left = CHART_PADDING_LEFT
        right = CHART_WIDTH - CHART_PADDING_RIGHT
        if extended[0][0] > left:
            extended.insert(0, (left, extended[0][1]))
        if extended[-1][0] < right:
            extended.append((right, extended[-1][1]))
        return extended
    if len(points) != 1:
        return points
    x, y = points[0]
    right_x = CHART_WIDTH - CHART_PADDING_RIGHT if full_width else max(x, CHART_PADDING_LEFT + 2)
    return [(CHART_PADDING_LEFT, y), (right_x, y)]


def svg_path(points: list[tuple[float, float]]) -> str:
    # Build an SVG polyline path from chart points.
    if not points:
        return ""
    head, *tail = points
    parts = [f"M {head[0]:.1f} {head[1]:.1f}"]
    parts.extend(f"L {x:.1f} {y:.1f}" for x, y in tail)
    return " ".join(parts)


def svg_area(points: list[tuple[float, float]]) -> str:
    # Build an SVG filled area under a metric line.
    if not points:
        return ""
    points = displayed_points(points)
    baseline = CHART_HEIGHT - CHART_PADDING_BOTTOM
    first_x = points[0][0]
    last_x = points[-1][0]
    return f"M {first_x:.1f} {baseline:.1f} L " + svg_path(points)[2:] + f" L {last_x:.1f} {baseline:.1f} Z"


def chart_axis_labels(snapshots: list[dict], window: ChartWindow) -> tuple[str, str]:
    # Choose start/end labels for the chart axis.
    if window.start is not None and window.end is not None:
        return (window.start.date().isoformat(), window.end.date().isoformat())
    if not snapshots:
        return ("", "")
    first = snapshots[0].get("date", "")[:10]
    last = snapshots[-1].get("date", "")[:10]
    return (first, last)


def axis_x_for_time(time: datetime, window: ChartWindow) -> float:
    # Map a timestamp into an SVG x coordinate inside the chart window.
    plot_width = CHART_WIDTH - CHART_PADDING_LEFT - CHART_PADDING_RIGHT
    if window.start is None or window.end is None:
        return CHART_PADDING_LEFT
    span = (window.end - window.start).total_seconds()
    if span <= 0:
        return CHART_PADDING_LEFT
    position = (time - window.start).total_seconds() / span
    return CHART_PADDING_LEFT + plot_width * min(max(position, 0), 1)


def short_month_day(time: datetime) -> str:
    # Format weekly tick labels.
    return f"{time.strftime('%b')} {time.day}"


def day_month(time: datetime) -> str:
    # Format compact timeframe labels.
    return f"{time.day} {time.strftime('%b')}"


def chart_week_ticks(window: ChartWindow) -> str:
    # Render weekly x-axis ticks across the chart window.
    if window.start is None or window.end is None:
        return ""
    ticks = []
    baseline = CHART_HEIGHT - CHART_PADDING_BOTTOM
    current = window.start
    while current <= window.end:
        x = axis_x_for_time(current, window)
        label = html_module.escape(short_month_day(current))
        ticks.append(
            f'<g class="progress-chart-tick" transform="translate({x:.1f} {baseline:.1f})">'
            f'<line y2="6"/>'
            f'<text x="{CHART_TICK_LABEL_X}" y="{CHART_TICK_LABEL_Y}" '
            f'transform="rotate(-38 {CHART_TICK_LABEL_X} {CHART_TICK_LABEL_Y})">{label}</text>'
            f'</g>'
        )
        current = current + timedelta(days=7)
    if ticks and current - timedelta(days=7) < window.end:
        x = axis_x_for_time(window.end, window)
        label = html_module.escape(short_month_day(window.end))
        ticks.append(
            f'<g class="progress-chart-tick" transform="translate({x:.1f} {baseline:.1f})">'
            f'<line y2="6"/>'
            f'<text x="{CHART_TICK_LABEL_X}" y="{CHART_TICK_LABEL_Y}" '
            f'transform="rotate(-38 {CHART_TICK_LABEL_X} {CHART_TICK_LABEL_Y})">{label}</text>'
            f'</g>'
        )
    return "".join(ticks)


def human_date(snapshot: dict) -> str:
    # Format a snapshot date for human-readable HTML text.
    parsed = snapshot_time(snapshot)
    if parsed is None:
        return html_module.escape(str(snapshot.get("date", ""))[:10])
    return html_module.escape(f"{parsed.strftime('%b')} {parsed.day}, {parsed.year}")


def tracking_days(snapshots: list[dict], window: ChartWindow) -> int:
    # Count the number of calendar days covered by the chart.
    if window.start is not None and window.end is not None:
        return max(1, (window.end.date() - window.start.date()).days + 1)
    dated = [time for time in (snapshot_time(snapshot) for snapshot in snapshots) if time is not None]
    if len(dated) < 2:
        return 1
    return max(1, (max(dated).date() - min(dated).date()).days + 1)


def chart_guides(snapshots: list[dict], kind: str, metrics: tuple[str, ...], max_value: int, window: ChartWindow) -> str:
    # Render horizontal guide lines for the latest metric values.
    guides = []
    latest = snapshots[-1]
    for metric in metrics:
        value = metric_value(latest, kind, metric)
        if value <= 0:
            continue
        points = chart_coordinates([latest], kind, metric, max_value, window)
        if not points:
            continue
        _x, y = points[-1]
        metric_class = html_module.escape(metric, quote=True)
        metric_text = html_module.escape(metric.title())
        guides.append(
            f'<line class="progress-chart-guide {metric_class}" '
            f'x1="{CHART_PADDING_LEFT}" y1="{y:.1f}" '
            f'x2="{CHART_WIDTH - CHART_PADDING_RIGHT}" y2="{y:.1f}">'
            f'<title>{metric_text}: {value}</title></line>'
        )
    return "".join(guides)


def chart_gridlines(max_value: int) -> str:
    # Render horizontal gridlines every five atoms.
    if max_value <= 5:
        return ""
    plot_height = CHART_HEIGHT - CHART_PADDING_TOP - CHART_PADDING_BOTTOM
    lines = []
    for value in range(5, max_value + 1, 5):
        y = CHART_PADDING_TOP + plot_height * (1 - value / max_value)
        lines.append(
            f'<g class="progress-chart-gridline">'
            f'<line x1="{CHART_PADDING_LEFT}" y1="{y:.1f}" '
            f'x2="{CHART_WIDTH - CHART_PADDING_RIGHT}" y2="{y:.1f}">'
            f'<title>{value} atoms</title></line>'
            f'<text x="{CHART_PADDING_LEFT - 8}" y="{y:.1f}">{value}</text>'
            f'</g>'
        )
    return "".join(lines)


def chart_timeframe(snapshots: list[dict], window: ChartWindow) -> str:
    # Summarize the tracked data range for the chart legend.
    if not snapshots:
        return ""
    first = snapshot_time(snapshots[0]) or window.start
    last = snapshot_time(snapshots[-1]) or window.end
    if first is None or last is None:
        return ""
    first_text = html_module.escape(day_month(first))
    last_text = html_module.escape(day_month(last))
    return f"{first_text} - {last_text}"


def progress_chart(title: str, kind: str, metrics: tuple[str, ...], snapshots: list[dict], window: ChartWindow, max_value: int) -> str:
    # Render one complete progress chart card.
    if not snapshots:
        return ""
    total_points = chart_coordinates(snapshots, kind, "total", max_value, window)
    total_path = html_module.escape(svg_path(displayed_points(total_points, full_width=True)), quote=True)
    metric_paths = []
    latest = snapshots[-1]
    legend_items = [f'<span><i class="progress-swatch total"></i>Total {metric_value(latest, kind, "total")}</span>']
    for metric in metrics:
        points = chart_coordinates(snapshots, kind, metric, max_value, window)
        path = html_module.escape(svg_path(displayed_points(points)), quote=True)
        area = html_module.escape(svg_area(points), quote=True)
        metric_class = html_module.escape(metric, quote=True)
        metric_label = html_module.escape(metric.title())
        metric_paths.append(f'<path class="progress-chart-area {metric_class}" d="{area}"/>')
        metric_paths.append(f'<path class="progress-chart-line {metric_class}" d="{path}"/>')
        metric_value_text = metric_value(latest, kind, metric)
        legend_items.append(f'<span><i class="progress-swatch {metric_class}"></i>{metric_label} {metric_value_text}</span>')
    timeframe_text = chart_timeframe(snapshots, window)
    title_text = html_module.escape(title)
    gridlines = chart_gridlines(max_value)
    guides = chart_guides(snapshots, kind, metrics, max_value, window)
    week_ticks = chart_week_ticks(window)
    if timeframe_text:
        legend_items.append(f'<span class="progress-chart-timeframe">{timeframe_text}</span>')
    legend = "".join(legend_items)
    metric_markup = "".join(metric_paths)
    return f'''
        <article class="progress-chart-card">
          <h3>{title_text}</h3>
          <svg class="progress-chart" viewBox="0 0 {CHART_WIDTH} {CHART_HEIGHT}" role="img" aria-label="{title_text} progress over time">
            <line class="progress-chart-axis" x1="{CHART_PADDING_LEFT}" y1="{CHART_HEIGHT - CHART_PADDING_BOTTOM}" x2="{CHART_WIDTH - CHART_PADDING_RIGHT}" y2="{CHART_HEIGHT - CHART_PADDING_BOTTOM}"/>
            <line class="progress-chart-axis" x1="{CHART_PADDING_LEFT}" y1="{CHART_PADDING_TOP}" x2="{CHART_PADDING_LEFT}" y2="{CHART_HEIGHT - CHART_PADDING_BOTTOM}"/>
            {gridlines}
            {guides}
            <path class="progress-chart-line total" d="{total_path}"/>
            {metric_markup}
            {week_ticks}
          </svg>
          <div class="progress-chart-legend">{legend}</div>
        </article>'''


def print_progress_charts(history_file: Path | None) -> None:
    # Print the Definitions and Theorems progress chart section.
    history = load_history_document(history_file)
    snapshots = sorted(history.get("snapshots", []), key=lambda snapshot: snapshot_time(snapshot) or datetime.min.replace(tzinfo=timezone.utc))
    if not snapshots:
        return
    window = chart_window(history, snapshots)
    max_value = chart_max_value(max(
        max(metric_value(snapshot, kind, "total") for snapshot in snapshots)
        for kind in ("definitions", "theorems")
    ))
    print('      <div class="progress-history" aria-label="Blueprint progress charts">')
    print('        <div class="progress-chart-grid">')
    print(progress_chart("Definitions", "definitions", ("specified",), snapshots, window, max_value))
    print(progress_chart("Theorems", "theorems", ("specified", "verified"), snapshots, window, max_value))
    print('        </div>')
    print('      </div>')


def print_html_summary(atoms: list[Atom], history_file: Path | None = None, site_dir: Path | None = None) -> None:
    # Print the root HTML status table, charts, and references section.
    chapters = summarize_by_chapter(atoms)
    ready_next_by_chapter = load_ready_next_by_chapter(site_dir) if site_dir is not None else {}
    current_blockers_by_chapter = load_current_blockers_by_chapter(site_dir) if site_dir is not None else {}
    atom_by_label = {atom.label: atom for atom in atoms}

    def items_by_kind_by_chapter(items_by_chapter: dict[str, list[ReadyNextItem]]) -> dict[str, dict[str, list[Atom]]]:
        atoms_by_chapter: dict[str, dict[str, list[Atom]]] = {}
        for chapter, items in items_by_chapter.items():
            kind_map: dict[str, list[Atom]] = {"definition": [], "theorem": []}
            for item in items:
                atom = atom_by_label.get(item.label)
                if atom is None:
                    continue
                kind_map[atom.kind].append(atom)
            atoms_by_chapter[chapter] = kind_map
        return atoms_by_chapter

    ready_next_atoms_by_chapter = items_by_kind_by_chapter(ready_next_by_chapter)
    current_blocker_atoms_by_chapter = items_by_kind_by_chapter(current_blockers_by_chapter)
    all_ready_next_definitions = [
        atom for chapter_map in ready_next_atoms_by_chapter.values() for atom in chapter_map["definition"]
    ]
    all_ready_next_theorems = [
        atom for chapter_map in ready_next_atoms_by_chapter.values() for atom in chapter_map["theorem"]
    ]
    all_current_blocker_theorems = [
        atom for chapter_map in current_blocker_atoms_by_chapter.values() for atom in chapter_map["theorem"]
    ]
    print('    <section class="blueprint-status" aria-labelledby="blueprint-status-heading">')
    print('      <h2 id="blueprint-status-heading">Blueprint Status and Progress</h2>')
    print_progress_charts(history_file)
    print('      <table class="status-table" aria-label="Per-chapter blueprint status">')
    print('        <thead>')
    print('          <tr><th scope="col" rowspan="2">Chapter</th><th scope="colgroup" colspan="3">Definitions</th><th class="theorem-group" scope="colgroup" colspan="5">Theorems</th></tr>')
    print('          <tr><th scope="col">Total</th><th scope="col">Specified</th><th scope="col">Ready next</th><th class="theorem-group" scope="col">Total</th><th scope="col">Specified</th><th scope="col">Ready next</th><th class="proof-group" scope="col">Verified</th><th scope="col">Proof blockers</th></tr>')
    print('        </thead>')
    print('        <tbody>')
    all_cells = "".join(
        [
            status_count_cell("ALL", "definition", "total", [atom for atom in atoms if atom.kind == "definition"]),
            status_count_cell("ALL", "definition", "specified", [atom for atom in atoms if atom.kind == "definition" and atom.specified]),
            status_count_cell("ALL", "definition", "ready next", all_ready_next_definitions),
            status_count_cell("ALL", "theorem", "total", [atom for atom in atoms if atom.kind == "theorem"], "theorem-group"),
            status_count_cell("ALL", "theorem", "specified", [atom for atom in atoms if atom.kind == "theorem" and atom.specified]),
            status_count_cell("ALL", "theorem", "ready next", all_ready_next_theorems),
            status_count_cell("ALL", "theorem", "verified", [atom for atom in atoms if atom.kind == "theorem" and atom.verified], "proof-group"),
            status_count_cell("ALL", "theorem", "proof blockers", all_current_blocker_theorems),
        ]
    )
    print(f'          <tr class="status-all-row"><th scope="row">ALL</th>{all_cells}</tr>')
    for chapter in sorted(chapters, key=chapter_sort_key):
        chapter_text = html_module.escape(chapter_title(chapter))
        definition_total = atoms_for(atoms, chapter, "definition", "total")
        definition_specified = atoms_for(atoms, chapter, "definition", "specified")
        theorem_total = atoms_for(atoms, chapter, "theorem", "total")
        theorem_specified = atoms_for(atoms, chapter, "theorem", "specified")
        theorem_verified = atoms_for(atoms, chapter, "theorem", "verified")
        cells = "".join(
            [
                status_count_cell(chapter, "definition", "total", definition_total),
                status_count_cell(chapter, "definition", "specified", definition_specified),
                status_count_cell(
                    chapter,
                    "definition",
                    "ready next",
                    ready_next_atoms_by_chapter.get(chapter, {}).get("definition", []),
                ),
                status_count_cell(chapter, "theorem", "total", theorem_total, "theorem-group"),
                status_count_cell(chapter, "theorem", "specified", theorem_specified),
                status_count_cell(
                    chapter,
                    "theorem",
                    "ready next",
                    ready_next_atoms_by_chapter.get(chapter, {}).get("theorem", []),
                ),
                status_count_cell(chapter, "theorem", "verified", theorem_verified, "proof-group"),
                status_count_cell(
                    chapter,
                    "theorem",
                    "proof blockers",
                    current_blocker_atoms_by_chapter.get(chapter, {}).get("theorem", []),
                ),
            ]
        )
        chapter_href = html_module.escape(f"{chapter}/", quote=True)
        print(f'          <tr><th scope="row"><a class="status-chapter-link" href="{chapter_href}">{chapter_text}</a></th>{cells}</tr>')
    print('        </tbody>')
    print('      </table>')
    print('      <section class="status-references" aria-labelledby="status-references-heading">')
    print('        <h3 id="status-references-heading">References</h3>')
    print('        <ul>')
    print('          <li class="status-ref-item"><a class="status-ref-title" href="https://eprint.iacr.org/2018/1037" target="_blank" rel="noreferrer noopener">The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol</a><span class="status-ref-authors">Joel Alwen, Sandro Coretti, Yevgeniy Dodis</span><span class="status-ref-venue">EUROCRYPT 2019</span></li>')
    print('          <li class="status-ref-item"><a class="status-ref-title" href="https://eprint.iacr.org/2025/078" target="_blank" rel="noreferrer noopener">Triple Ratchet: A Bandwidth-Efficient Hybrid-Secure Signal Protocol</a><span class="status-ref-authors">Yevgeniy Dodis, Daniel Jost, Shuichi Katsumata, Thomas Prest, Sebastian Schmidt</span><span class="status-ref-venue">EUROCRYPT 2025</span></li>')
    print('          <li class="status-ref-item"><a class="status-ref-title" href="https://eprint.iacr.org/2025/2267" target="_blank" rel="noreferrer noopener">How to Compare Bandwidth-Constrained Two-Party Secure Messaging Protocols: A Quest for a More Efficient and Secure Post-Quantum Protocol</a><span class="status-ref-authors">Benedikt Auerbach, Yevgeniy Dodis, Daniel Jost, Shuichi Katsumata, Sebastian Schmidt</span><span class="status-ref-venue">USENIX Security 2025</span></li>')
    print('          <li class="status-ref-item"><a class="status-ref-title" href="https://github.com/Verified-zkEVM/VCV-io" target="_blank" rel="noreferrer noopener">VCV-io</a><span class="status-ref-authors">Formalized Cryptography Proofs in Lean 4</span><span class="status-ref-venue">GitHub Repository</span></li>')
    print('          <li class="status-ref-item"><a class="status-ref-title" href="https://github.com/Beneficial-AI-Foundation/secure-messaging" target="_blank" rel="noreferrer noopener">secure-messaging (project source)</a><span class="status-ref-authors">Lean/VCVio specifications and proofs for secure messaging protocols</span><span class="status-ref-venue">GitHub Repository</span></li>')
    print('        </ul>')
    print('      </section>')
    print('    </section>')


def json_report(atoms: list[Atom]) -> dict:
    # Build a machine-readable summary of atom status.
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
    # Parse CLI options and choose text, JSON, or HTML output.
    parser = argparse.ArgumentParser(description="Aggregate Verso blueprint atom status from rendered chapter manifests.")
    parser.add_argument("--site-dir", type=Path, default=DEFAULT_SITE_DIR)
    parser.add_argument("--docs-dir", type=Path, default=DEFAULT_DOCS_DIR)
    parser.add_argument("--all-atoms", action="store_true", help="Report every rendered Blueprint atom, including untracked helpers.")
    parser.add_argument("--by-chapter", action="store_true")
    parser.add_argument("--html-summary", action="store_true")
    parser.add_argument("--history-file", type=Path)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args()

    atoms = load_atoms(args.site_dir) if args.all_atoms else load_tracked_atoms(args.site_dir, args.docs_dir)
    if args.html_summary:
        print_html_summary(atoms, args.history_file, args.site_dir)
    elif args.as_json:
        print(json.dumps(json_report(atoms), indent=2, sort_keys=True))
    else:
        print_text_report(atoms, args.by_chapter)


if __name__ == "__main__":
    main()