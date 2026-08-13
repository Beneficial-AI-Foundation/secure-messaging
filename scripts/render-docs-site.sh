#!/usr/bin/env bash
set -euo pipefail

# Render each documentation chapter as its own Verso manual and combine the
# outputs into one static site.
output_root="_out/site"

# By default, render the deployable site under `_out/site`. Pass
# `--output <dir>` for local preview builds in a separate directory.
while [[ $# -gt 0 ]]; do
  case "$1" in
    --output)
      output_root="$2"
      shift 2
      ;;
    *)
      echo "unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

site_root="$output_root/html-multi"
render_root="$output_root/chapter-renders"
history_root="$output_root/history"
previous_history="$history_root/blueprint-progress-history.json"
docs_root="docs/SecureMessagingDocs"

# Recover prior progress history when available.
recover_previous_progress_history() {
  rm -f "$previous_history"
  mkdir -p "$history_root"

  # Use an explicit local history file when provided.
  if [[ -n "${BLUEPRINT_PROGRESS_HISTORY_FILE:-}" && -f "${BLUEPRINT_PROGRESS_HISTORY_FILE:-}" ]]; then
    cp "$BLUEPRINT_PROGRESS_HISTORY_FILE" "$previous_history"
    echo "Recovered Blueprint progress history from $BLUEPRINT_PROGRESS_HISTORY_FILE"
    return
  fi

  # Otherwise, fetch from the deployed site when a URL is provided.
  if [[ -n "${BLUEPRINT_PROGRESS_HISTORY_URL:-}" ]]; then
    if curl -fsSL "$BLUEPRINT_PROGRESS_HISTORY_URL" -o "$previous_history"; then
      echo "Recovered Blueprint progress history from $BLUEPRINT_PROGRESS_HISTORY_URL"
      return
    fi
    echo "No deployed Blueprint progress history found at $BLUEPRINT_PROGRESS_HISTORY_URL" >&2
  fi

  echo "Starting Blueprint progress history from the current render"
}

# Decide whether recovered history can be extended or has to be rebuilt.
# Snapshot totals are not checked: the tracked atom set grows as atoms gain
# issue footers, so historical totals differ from today's by design.
history_reseed_reason() {
  local history_file="$1"
  python3 - "$history_file" <<'PY'
import json
import sys
from pathlib import Path

history_path = Path(sys.argv[1])
expected_schema = 2
expected_basis = "linked closing PR merge dates"

if not history_path.exists():
    print("missing")
    raise SystemExit

try:
    data = json.loads(history_path.read_text())
except Exception:
    print("invalid")
    raise SystemExit

if not isinstance(data, dict):
    print("stale-schema")
    raise SystemExit

snapshots = data.get("snapshots", [])
if not isinstance(snapshots, list) or len(snapshots) < 2:
    print("sparse")
    raise SystemExit

if data.get("schemaVersion") != expected_schema:
    print("stale-schema")
    raise SystemExit

if expected_basis not in str(data.get("historyBasis", "")):
    print("stale-basis")
    raise SystemExit

# Per-commit attribution reads the labels behind each count. Without them a
# snapshot cannot say which atoms were already reached, and the next one would
# claim all of them.
for snapshot in snapshots:
    for kind in ("definitions", "theorems"):
        counts = snapshot.get(kind, {}) if isinstance(snapshot, dict) else {}
        if not all(isinstance(counts.get(f"{metric}Labels"), list) for metric in ("specified", "verified")):
            print("missing-labels")
            raise SystemExit

print("none")
PY
}

# Seed progress history when recovery is missing or too sparse; set the flag to 0 to skip.
seed_progress_history_if_needed() {
  if [[ "${BLUEPRINT_PROGRESS_HISTORY_SEED:-1}" != "1" ]]; then
    return
  fi

  local reseed_reason
  reseed_reason="$(history_reseed_reason "$previous_history")"
  if [[ "$reseed_reason" == "none" ]]; then
    return
  fi

  if ! command -v gh >/dev/null 2>&1; then
    echo "Cannot seed Blueprint progress history: gh is not available" >&2
    return
  fi

  echo "Reseeding Blueprint progress history ($reseed_reason) from GitHub issue closures and closing PRs"

  if python3 scripts/seed-blueprint-progress-history.py \
    --site-dir "$site_root" \
    --docs-dir "$docs_root" \
    --history "$previous_history"; then
    echo "Seeded Blueprint progress history from GitHub issue closures and closing PRs"
  else
    echo "Could not seed Blueprint progress history; using current render only" >&2
  fi
}

# Verso renders each chapter as a standalone manual. Add a project-level link to
# every page sidebar and inject the small bits of shared styling needed by the
# combined site.
add_project_index_links() {
  local chapter_dir="$1"
  local contents_label="$2"
  while IFS= read -r -d '' html_file; do
    CHAPTER_CONTENTS="$contents_label" perl -0pi -e '
    my $contents = $ENV{"CHAPTER_CONTENTS"} // "Chapter Contents:";
    my $chapterHref = "./";
    s{</head>}{<style>\n#toc .project-index-toc {\n  margin-bottom: 0.75rem;\n}\n#toc .project-index-toc a {\n  color: inherit;\n  font-weight: 600;\n  text-decoration: none;\n}\n#toc .project-index-toc a:hover {\n  text-decoration: underline;\n}\n.chapter-overview-actions {\n  display: flex;\n  flex-wrap: wrap;\n  gap: 0.55rem;\n  margin: 1rem 0 0;\n}\n.chapter-overview-actions a {\n  display: inline-block;\n  padding: 0.34rem 0.65rem;\n  border: 1px solid #d0d7de;\n  border-radius: 6px;\n  background: #f6f8fa;\n  color: #556070;\n  font-size: 0.9rem;\n  font-weight: 600;\n  text-decoration: none;\n}\n.chapter-overview-actions a:hover {\n  border-color: #9fb0cf;\n  color: #1f2937;\n}\n</style>\n</head>};
    s{\s*<div class="bp_build_metadata" aria-label="Build metadata">.*?</div>\s*}{}s;
    s{\s*<h2>\s*Contents\s*</h2>}{}s;
    if (!/<div class="split-toc project-index-toc">/) {
      s{<div class="split-toc book">\s*<div class="title">}{<div class="split-toc project-index-toc">\n              <div class="title">\n                <span class="no-toggle"></span><span class=""><a href="../">Table of Contents</a></span>\n                </div>\n              </div>\n            <div class="split-toc book">\n              <div class="title">};
    }
    s{(<span class="">)Table of Contents(</span>)}{$1<a href="$chapterHref">$contents</a>$2};
  ' "$html_file"
  done < <(find "$chapter_dir" -name '*.html' -type f -print0)
}

# Split chapter manuals emit a standalone title page. Remove it from chapter
# overview pages because the combined site already shows the chapter title.
remove_generated_manual_titlepage() {
  local index_file="$1"
  perl -0pi -e '
    s{\s*<div class="titlepage">\s*<h1>.*?</h1>\s*(?:<div class="authors"></div>\s*)?</div>\s*}{}s;
  ' "$index_file"
}

# Chapter pages begin with references when the source manual starts with
# `*References:*`. Move that block to the bottom of the page so definitions and
# theorem statements are the first content a reader sees. On overview pages, the
# generated Graph/Summary links are folded into compact action buttons.
move_references_to_bottom() {
  local chapter_dir="$1"
  while IFS= read -r -d '' html_file; do
    perl -0pi -e '
    my $refs = "";
    my $graph_summary = "";
    if (s{(\s*<p>\s*<strong>References:</strong>\s*</p>\s*<ul>.*?</ul>\s*)}{}s) {
      $refs = $1;
      s{(\s*<li>\s*<a href="Dependency-Graph/.*?</li>\s*<li>\s*<a href="Blueprint-Summary/.*?</li>\s*)}{ $graph_summary = $1; "" }se;
      my @links = ();
      while ($graph_summary =~ m{<a href="([^"]+)">(?:<span class="unnumbered"></span>)?([^<]+)</a>}g) {
        push @links, qq{<a href="$1">$2</a>};
      }
      my $actions = @links ? qq{<div class="chapter-overview-actions">} . join("", @links) . qq{</div>} : "";
      my $bottom = $refs . $actions;
      if (!s{(\s*</section>\s*<nav class="prev-next-buttons">)}{$bottom$1}s) {
        s{(\s*</section>\s*</div>\s*</main>)}{$bottom$1}s;
      }
    }
  ' "$html_file"
  done < <(find "$chapter_dir" -name '*.html' -type f -print0)
}

# runner | overview module | output slug | site title | sidebar contents label
chapters=(
  "docs/SecureMessagingDocs/Renderers/AEADMain.lean|SecureMessagingDocs.Chapters.AEAD.Overview|Authenticated-Encryption-with-Associated-Data|Authenticated Encryption with Associated Data|AEAD Contents:"
  "docs/SecureMessagingDocs/Renderers/CKAMain.lean|SecureMessagingDocs.Chapters.CKA.Overview|Continuous-Key-Agreement|Continuous Key Agreement|CKA Contents:"
  "docs/SecureMessagingDocs/Renderers/ErasureCodesMain.lean|SecureMessagingDocs.Chapters.ErasureCodes.Overview|Erasure-Codes|Erasure Codes|Erasure Codes Contents:"
  "docs/SecureMessagingDocs/Renderers/FSAEADMain.lean|SecureMessagingDocs.Chapters.FSAEAD.Overview|Forward-Secure-AEAD|Forward-Secure Authenticated Encryption with Associated Data|FS-AEAD Contents:"
  "docs/SecureMessagingDocs/Renderers/PRFPRNGMain.lean|SecureMessagingDocs.Chapters.PRFPRNG.Overview|PRF-PRNG|Pseudorandom Function and Generator|PRF-PRNG Contents:"
  "docs/SecureMessagingDocs/Renderers/KEMMain.lean|SecureMessagingDocs.Chapters.KEM.Overview|Key-Encapsulation-Mechanism|Key Encapsulation Mechanism|KEM Contents:"
  "docs/SecureMessagingDocs/Renderers/RKEMMain.lean|SecureMessagingDocs.Chapters.RKEM.Overview|Ratcheting-KEM|Ratcheting Key Encapsulation Mechanism|RKEM Contents:"
  "docs/SecureMessagingDocs/Renderers/SCKAMain.lean|SecureMessagingDocs.Chapters.SCKA.Overview|Sparse-Continuous-Key-Agreement|Sparse Continuous Key Agreement|SCKA Contents:"
  "docs/SecureMessagingDocs/Renderers/SecureMessagingMain.lean|SecureMessagingDocs.Chapters.SecureMessaging.Overview|Secure-Messaging|Secure Messaging|Secure Messaging Contents:"
)

rm -rf "$site_root" "$render_root"
mkdir -p "$site_root" "$render_root"
recover_previous_progress_history

# The site root is intentionally plain HTML: chapter manuals remain responsible
# for their own Verso assets, search indexes, graphs, and previews.
cat > "$site_root/index.html" <<'HTML'
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Secure Messaging — Lean Formalization</title>
  <style>
    :root {
      color-scheme: light;
      --text: #172033;
      --muted: #5d677a;
      --line: #d7dde8;
      --link: #2457c5;
      --bg: #ffffff;
      --panel: #f7f9fc;
    }
    body {
      margin: 0;
      font-family: system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      color: var(--text);
      background: var(--bg);
      line-height: 1.55;
    }
    main {
      max-width: 1416px;
      margin: 0 auto;
      padding: 56px 28px 72px;
    }
    h1 {
      margin: 0 0 8px;
      font-size: clamp(2rem, 6vw, 3.2rem);
      line-height: 1.05;
      letter-spacing: 0;
    }
    .subtitle {
      margin: 0 0 32px;
      max-width: none;
      color: var(--muted);
      font-size: 1.05rem;
    }
    .chapter-list {
      display: grid;
      gap: 10px;
      margin: 0;
      padding: 0;
      list-style: none;
    }
    .chapter-row {
      display: flex;
      justify-content: space-between;
      align-items: center;
      gap: 16px;
      padding: 13px 15px;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--panel);
    }
    .chapter-row:hover {
      border-color: #9fb0cf;
    }
    .chapter-title {
      color: var(--text);
      text-decoration: none;
      font-weight: 600;
    }
    .chapter-title:hover {
      text-decoration: underline;
    }
    .blueprint-status {
      margin-top: 34px;
    }
    .blueprint-status h2 {
      margin: 0 0 14px;
      font-size: 1.45rem;
    }
    .status-summary {
      display: grid;
      grid-template-columns: repeat(2, minmax(0, 1fr));
      gap: 12px;
      margin-bottom: 16px;
    }
    .status-card {
      padding: 15px;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--panel);
    }
    .status-card h3 {
      margin: 0 0 10px;
      font-size: 1rem;
    }
    .status-card dl {
      display: grid;
      gap: 8px;
      margin: 0;
    }
    .status-card dl div {
      display: flex;
      justify-content: space-between;
      gap: 12px;
    }
    .status-card dt {
      color: var(--muted);
    }
    .status-card dd {
      margin: 0;
      font-weight: 700;
    }
    .status-table {
      width: 100%;
      min-width: 820px;
      margin-top: 34px;
      border-collapse: collapse;
      border: 1px solid var(--line);
      font-size: 0.95rem;
    }
    .status-table caption {
      margin-bottom: 8px;
      color: var(--muted);
      text-align: left;
    }
    .status-table th,
    .status-table td {
      padding: 9px 10px;
      border-top: 1px solid var(--line);
      text-align: left;
    }
    .status-table th:not(:first-child),
    .status-table td {
      text-align: center;
      vertical-align: middle;
    }
    .status-table th[colspan] {
      text-align: center;
    }
    .status-table .theorem-group {
      border-left: 2px solid var(--line);
    }
    .status-chapter-link {
      color: inherit;
      text-decoration: none;
    }
    .status-chapter-link:hover,
    .status-chapter-link:focus {
      text-decoration: underline;
      text-underline-offset: 0.15em;
    }
    .status-count {
      position: relative;
      display: inline-flex;
      justify-content: center;
      min-width: 1.6rem;
      cursor: pointer;
      outline: none;
    }
    .status-number {
      color: var(--link);
      font-weight: 700;
      text-decoration: underline;
      text-decoration-thickness: 1px;
      text-underline-offset: 2px;
    }
    .status-popover {
      position: absolute;
      top: calc(100% + 8px);
      right: 0;
      z-index: 20;
      display: none;
      width: max-content;
      max-width: min(360px, 82vw);
      max-height: 280px;
      overflow: auto;
      padding: 10px 12px;
      border: 1px solid #b8c2d4;
      border-radius: 6px;
      background: #ffffff;
      box-shadow: 0 12px 32px rgba(23, 32, 51, 0.16);
      color: var(--text);
      text-align: left;
      white-space: normal;
    }
    .status-popover strong {
      display: block;
      margin-bottom: 7px;
      font-size: 0.85rem;
    }
    .status-popover ul {
      display: grid;
      gap: 5px;
      margin: 0;
      padding-left: 1.1rem;
    }
    .status-popover a {
      color: var(--link);
    }
    .status-popover code {
      font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace;
      font-size: 0.84rem;
    }
    .status-popover li span {
      color: var(--muted);
      font-size: 0.82rem;
    }
    .status-count:hover .status-popover,
    .status-count:focus .status-popover,
    .status-count:focus-within .status-popover {
      display: block;
    }
    .status-table thead th {
      border-top: 0;
      background: var(--panel);
      color: var(--muted);
      font-weight: 600;
    }
    .status-table .status-all-row th,
    .status-table .status-all-row td {
      border-top: 2px solid #9fb0cf;
      border-bottom: 2px solid #9fb0cf;
      background: #eef3fb;
      font-weight: 800;
      padding-top: 11px;
      padding-bottom: 11px;
    }
    .progress-history {
      margin-top: 34px;
    }
    .progress-history h2 {
      margin: 0 0 14px;
      font-size: 1.45rem;
    }
    .progress-chart-grid {
      display: grid;
      grid-template-columns: 1fr;
      gap: 22px;
    }
    .progress-chart-card {
      padding: 18px 18px 16px;
      border: 1px solid var(--line);
      border-radius: 8px;
      background: var(--panel);
      overflow-x: auto;
      scrollbar-gutter: stable;
    }
    .progress-chart-wrap {
      position: relative;
    }
    .progress-chart {
      display: block;
      width: 100%;
      min-width: 760px;
      min-height: 360px;
      height: auto;
      overflow: visible;
    }
    .progress-chart-hit {
      cursor: pointer;
      outline: none;
    }
    .progress-chart-hitarea {
      fill: transparent;
    }
    .progress-chart-crosshair {
      stroke: #64748b;
      stroke-width: 1.4;
      stroke-dasharray: 3 5;
      opacity: 0;
      pointer-events: none;
    }
    .progress-chart-dot {
      stroke: var(--panel);
      stroke-width: 1.8;
      paint-order: stroke fill;
      opacity: 0.95;
      pointer-events: none;
    }
    .progress-chart-dot.total {
      fill: #5b6474;
    }
    .progress-chart-dot.specified {
      fill: #2563eb;
    }
    .progress-chart-dot.verified {
      fill: #16a34a;
    }
    .progress-chart-card:not(.is-hovering) .progress-chart-hit:last-child .progress-chart-dot {
      opacity: 1;
    }
    .progress-chart-hit.is-active .progress-chart-crosshair,
    .progress-chart-hit:focus-visible .progress-chart-crosshair {
      opacity: 0.85;
    }
    .progress-chart-hit.is-active .progress-chart-dot,
    .progress-chart-hit:focus-visible .progress-chart-dot,
    .progress-chart-hit.is-pinned .progress-chart-dot {
      opacity: 1;
    }
    .progress-chart-hit.is-pinned .progress-chart-crosshair {
      stroke: var(--link);
      stroke-dasharray: none;
      opacity: 0.7;
    }
    .progress-chart-card.is-hovering .progress-chart-hit:not(.is-active):not(.is-pinned) {
      opacity: 0.35;
    }
    .progress-chart-panel {
      padding: 0.7rem 0.8rem;
      border: 1px solid #9fb0cf;
      border-radius: 8px;
      background: rgba(255, 255, 255, 0.98);
      color: var(--text);
      box-shadow: 0 10px 28px rgba(23, 32, 51, 0.12);
    }
    .progress-chart-tooltip {
      position: absolute;
      z-index: 4;
      display: flex;
      flex-wrap: wrap;
      align-items: flex-start;
      gap: 10px;
      max-width: min(46rem, calc(100% - 1.2rem));
      /* A preview only: it trails the cursor, so it must never catch events. */
      pointer-events: none;
    }
    .progress-chart-tooltip .progress-chart-panel {
      flex: 1 1 13rem;
      min-width: 12.5rem;
      max-width: 22rem;
    }
    .progress-chart-tooltip[hidden] {
      display: none !important;
    }
    .progress-chart-pins {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(16rem, 1fr));
      align-items: start;
      gap: 12px;
      margin-top: 12px;
    }
    .progress-chart-pins[hidden] {
      display: none !important;
    }
    .progress-chart-pin {
      position: relative;
      border-color: var(--link);
      box-shadow: 0 8px 22px rgba(23, 32, 51, 0.14);
    }
    .progress-chart-pin > strong {
      padding-right: 1.4rem;
    }
    .progress-chart-pin-close {
      position: absolute;
      top: 0.3rem;
      right: 0.35rem;
      width: 1.4rem;
      height: 1.4rem;
      padding: 0;
      border: 0;
      border-radius: 4px;
      background: transparent;
      color: var(--muted);
      font-size: 1.1rem;
      line-height: 1;
      cursor: pointer;
    }
    .progress-chart-pin-close:hover,
    .progress-chart-pin-close:focus-visible {
      background: rgba(36, 87, 197, 0.1);
      color: var(--link);
    }
    .progress-chart-panel strong {
      display: block;
      margin-bottom: 0.35rem;
      font-size: 0.95rem;
    }
    .progress-chart-panel dl {
      display: grid;
      grid-template-columns: auto 1fr;
      gap: 0.18rem 0.7rem;
      margin: 0;
    }
    .progress-chart-panel dt {
      color: var(--muted);
      font-size: 0.82rem;
      font-weight: 650;
    }
    .progress-chart-panel dd {
      margin: 0;
      font-size: 0.9rem;
      font-weight: 700;
      text-align: right;
    }
    .progress-chart-panel .progress-chart-tooltip-meta {
      margin: 0.45rem 0 0;
      color: var(--muted);
      font-size: 0.8rem;
      line-height: 1.35;
    }
    .progress-chart-tooltip-atoms ul {
      max-height: 8.5rem;
    }
    .progress-chart-tooltip-meta a {
      color: var(--link);
      text-decoration: none;
    }
    .progress-chart-tooltip-meta a:hover {
      text-decoration: underline;
    }
    .progress-chart-tooltip-ref {
      font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
      font-weight: 700;
    }
    .progress-chart-tooltip-atoms {
      margin-top: 0.4rem;
    }
    .progress-chart-tooltip-atoms-title {
      display: block;
      margin-bottom: 0.3rem;
      color: var(--muted);
      font-size: 0.78rem;
      font-weight: 700;
      letter-spacing: 0.02em;
      text-transform: uppercase;
    }
    .progress-chart-tooltip-atoms ul {
      display: grid;
      gap: 0.28rem;
      max-height: 11rem;
      overflow-y: auto;
      margin: 0;
      padding-left: 1.05rem;
    }
    .progress-chart-tooltip-atoms li {
      font-size: 0.84rem;
      line-height: 1.3;
    }
    .progress-chart-tooltip-atoms a {
      color: var(--link);
    }
    .progress-chart-tooltip-atoms code {
      font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
      font-size: 0.82rem;
    }
    .progress-chart-tooltip-atoms .progress-chart-tooltip-atom-note {
      display: block;
      color: var(--muted);
      font-size: 0.78rem;
    }
    .progress-chart-axis {
      stroke: #5d6b7f;
      stroke-width: 2.9;
      stroke-linecap: square;
    }
    .progress-chart-gridline line {
      stroke: #c8d1df;
      stroke-dasharray: 3 7;
      stroke-linecap: round;
      stroke-width: 1;
      opacity: 0.74;
    }
    .progress-chart-gridline text {
      dominant-baseline: middle;
      fill: #334155;
      font-size: 0.9rem;
      font-weight: 800;
      paint-order: stroke fill;
      stroke: var(--panel);
      stroke-linejoin: round;
      stroke-width: 3px;
      text-anchor: end;
    }
    .progress-chart-guide {
      stroke-dasharray: 3 5;
      stroke-linecap: round;
      stroke-width: 1.7;
      opacity: 0.58;
    }
    .progress-chart-guide.specified {
      stroke: #2563eb;
    }
    .progress-chart-guide.verified {
      stroke: #16a34a;
    }
    .progress-chart-line {
      fill: none;
      stroke-linecap: round;
      stroke-linejoin: round;
      stroke-width: 4.8;
    }
    .progress-chart-line.total {
      stroke: #5b6474;
      stroke-dasharray: 5 5;
    }
    .progress-chart-line.specified {
      stroke: #2563eb;
    }
    .progress-chart-line.verified {
      stroke: #16a34a;
    }
    .progress-chart-area {
      opacity: 0.32;
    }
    .progress-chart-area.specified {
      fill: #2563eb;
    }
    .progress-chart-area.verified {
      fill: #16a34a;
    }
    .progress-chart-label {
      fill: var(--muted);
      font-size: 0.86rem;
    }
    .progress-chart-tick line {
      stroke: #66758a;
      stroke-width: 1.7;
    }
    .progress-chart-tick text {
      fill: #334155;
      font-family: ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      font-size: 0.98rem;
      font-weight: 700;
      paint-order: stroke fill;
      stroke: var(--panel);
      stroke-linejoin: round;
      stroke-width: 3px;
      dominant-baseline: hanging;
      text-anchor: end;
    }
    .progress-chart-legend {
      display: flex;
      align-items: center;
      flex-wrap: nowrap;
      gap: 14px;
      margin-top: 12px;
      overflow-x: auto;
      white-space: nowrap;
      color: var(--muted);
      font-size: 1rem;
      font-weight: 650;
    }
    .progress-chart-legend span {
      display: inline-flex;
      align-items: center;
      gap: 5px;
    }
    .progress-chart-timeframe {
      margin-left: auto;
      color: var(--muted);
      font-weight: 600;
    }
    .progress-swatch {
      width: 16px;
      height: 4px;
      border-radius: 999px;
      background: #5b6474;
    }
    .progress-swatch.specified {
      background: #2563eb;
    }
    .progress-swatch.verified {
      background: #16a34a;
    }
    .status-references {
      margin-top: 16px;
      padding: 14px 15px;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--panel);
    }
    .status-references h3 {
      margin: 0 0 8px;
      font-size: 1rem;
    }
    .status-references ul {
      margin: 0;
      padding-left: 1.05rem;
      display: grid;
      gap: 10px;
    }
    .status-ref-item {
      display: grid;
      gap: 2px;
      color: #1f2937;
    }
    .status-ref-title {
      color: #1f2937;
      font-family: "Iowan Old Style", "Palatino Linotype", Palatino, "Times New Roman", serif;
      font-size: 1.02rem;
      font-style: italic;
      text-decoration-color: currentColor;
      text-underline-offset: 0.15em;
    }
    .status-ref-authors {
      font-family: "Avenir Next", "Helvetica Neue", "Segoe UI", sans-serif;
      font-size: 0.9rem;
      color: #556070;
    }
    .status-ref-venue {
      font-family: "Courier Prime", "Courier New", ui-monospace, monospace;
      font-size: 0.84rem;
      letter-spacing: 0.05em;
      text-transform: uppercase;
      color: #334155;
    }
    @media (max-width: 640px) {
      .chapter-row {
        align-items: flex-start;
        flex-direction: column;
      }
      .status-summary {
        grid-template-columns: 1fr;
      }
      .status-table {
        font-size: 0.85rem;
      }
      .progress-chart {
        min-width: 640px;
        min-height: 300px;
      }
    }
    footer {
      margin-top: 34px;
      color: var(--muted);
      font-size: 0.95rem;
    }
    footer a {
      color: var(--link);
    }
  </style>
</head>
<body>
  <main>
    <h1>Secure Messaging</h1>
    <p class="subtitle">Formal verification of cryptographic primitives and protocols for secure messaging in Lean</p>
    <ul class="chapter-list">
HTML

for chapter in "${chapters[@]}"; do
  IFS='|' read -r runner module slug title contents_label <<< "$chapter"
  echo "Rendering $title"

  # Render one chapter manual into a temporary directory, then copy only its
  # html-multi output into the assembled site. The helpers below normalize each
  # standalone manual so it behaves like one chapter of the combined site.
  out_dir="$render_root/$slug"
  lake build SecureMessagingDocs.Render "$module"
  lake env lean --run "$runner" --output "$out_dir"
  mkdir -p "$site_root/$slug"
  cp -R "$out_dir/html-multi/." "$site_root/$slug/"
  add_project_index_links "$site_root/$slug" "$contents_label"
  move_references_to_bottom "$site_root/$slug"
  remove_generated_manual_titlepage "$site_root/$slug/index.html"
  printf '      <li><div class="chapter-row"><a class="chapter-title" href="%s/">%s</a></div></li>\n' "$slug" "$title" >> "$site_root/index.html"
done

# The chapters are rendered independently, so Verso cannot resolve Blueprint
# `uses` links that point into a different chapter. Repair those placeholders
# once all per-chapter manifests and HTML files are present in the combined site.
python3 scripts/resolve-split-blueprint-uses.py --site-dir "$site_root"
seed_progress_history_if_needed

cat >> "$site_root/index.html" <<'HTML'
    </ul>
HTML

# Build the root Blueprint status table from the same per-chapter manifests.
# This avoids importing every rich documentation module into one giant manual.
python3 scripts/update-blueprint-progress-history.py \
  --site-dir "$site_root" \
  --docs-dir "$docs_root" \
  --history "$previous_history" \
  --output "$site_root/blueprint-progress-history.json"
python3 scripts/aggregate-blueprint-status.py \
  --site-dir "$site_root" \
  --docs-dir "$docs_root" \
  --history-file "$site_root/blueprint-progress-history.json" \
  --html-summary >> "$site_root/index.html"

cat >> "$site_root/index.html" <<'HTML'
  </main>
  <script>
    (function () {
      function escapeHtml(value) {
        return String(value)
          .replace(/&/g, "&amp;")
          .replace(/</g, "&lt;")
          .replace(/>/g, "&gt;")
          .replace(/"/g, "&quot;");
      }

      // Each commit reports the state it left behind; the day's own attributes
      // are the fallback when a point carries no commit detail.
      function metricRows(hit, metrics, values) {
        return metrics.map(function (metric) {
          var raw = values && values[metric] !== undefined
            ? values[metric]
            : hit.getAttribute("data-" + metric);
          if (raw === null || raw === undefined || raw === "") return "";
          var label = metric.charAt(0).toUpperCase() + metric.slice(1);
          return "<dt>" + escapeHtml(label) + "</dt><dd>" + escapeHtml(raw) + "</dd>";
        }).join("");
      }

      function commits(hit) {
        var raw = hit.getAttribute("data-commits");
        if (!raw) return [];
        try {
          var parsed = JSON.parse(raw);
          return Array.isArray(parsed) ? parsed : [];
        } catch (error) {
          return [];
        }
      }

      function newAtomsHtml(atoms) {
        if (!atoms || !atoms.length) return "";
        var items = atoms.map(function (atom) {
          var name = "<code>" + escapeHtml(atom.label || "") + "</code>";
          // Atoms added after the last render have no manifest entry to link to.
          var body = atom.href
            ? '<a href="' + escapeHtml(atom.href) + '">' + name + "</a>"
            : name;
          var note = [atom.title].concat(atom.metrics || []).filter(Boolean).join(" · ");
          return (
            "<li>" + body +
            (note ? '<span class="progress-chart-tooltip-atom-note">' + escapeHtml(note) + "</span>" : "") +
            "</li>"
          );
        }).join("");
        return (
          '<div class="progress-chart-tooltip-atoms">' +
          '<span class="progress-chart-tooltip-atoms-title">New atoms (' + atoms.length + ")</span>" +
          "<ul>" + items + "</ul></div>"
        );
      }

      function commitHtml(entry) {
        var ref = entry.ref || "";
        var body =
          (ref ? '<span class="progress-chart-tooltip-ref">' + escapeHtml(ref) + "</span>" : "") +
          (entry.subject ? (ref ? " " : "") + escapeHtml(entry.subject) : "");
        return (
          (body
            ? '<p class="progress-chart-tooltip-meta">' +
              (entry.url
                ? '<a href="' + escapeHtml(entry.url) + '" target="_blank" rel="noopener">' + body + "</a>"
                : body) +
              "</p>"
            : "") +
          newAtomsHtml(entry.newAtoms)
        );
      }

      // A day can hold several merges. Give each one its own box so they sit
      // side by side rather than stacking inside a single card.
      function dayBoxes(hit, metrics) {
        var heading = "<strong>" + escapeHtml(hit.getAttribute("data-date") || "") + "</strong>";
        var entries = commits(hit);
        if (!entries.length) {
          return [heading + "<dl>" + metricRows(hit, metrics, null) + "</dl>"];
        }
        return entries.map(function (entry) {
          return (
            heading +
            "<dl>" + metricRows(hit, metrics, entry.metrics) + "</dl>" +
            commitHtml(entry)
          );
        });
      }

      // Track the cursor so the card sits clear of the series line and leaves the
      // neighbouring points visible.
      function positionTooltip(wrap, tooltip, hit, event) {
        var wrapRect = wrap.getBoundingClientRect();
        var tipWidth = tooltip.offsetWidth || 200;
        var tipHeight = tooltip.offsetHeight || 120;
        var gap = 16;
        var anchorX;
        var anchorY;
        if (event && typeof event.clientX === "number") {
          anchorX = event.clientX - wrapRect.left;
          anchorY = event.clientY - wrapRect.top;
        } else {
          // Keyboard focus has no cursor, so anchor under the point itself.
          var hitRect = hit.getBoundingClientRect();
          anchorX = hitRect.left + hitRect.width / 2 - wrapRect.left;
          anchorY = hitRect.top + hitRect.height / 2 - wrapRect.top;
        }
        var left = anchorX + gap;
        var top = anchorY + gap;
        // Flip to the other side of the cursor rather than sliding over the chart.
        if (left + tipWidth > wrapRect.width - 8) {
          left = Math.max(8, anchorX - gap - tipWidth);
        }
        if (top + tipHeight > wrapRect.height - 8) {
          top = Math.max(8, anchorY - gap - tipHeight);
        }
        tooltip.style.left = left + "px";
        tooltip.style.top = top + "px";
      }

      function bindCard(card) {
        var wrap = card.querySelector(".progress-chart-wrap");
        var tooltip = card.querySelector(".progress-chart-tooltip");
        var pins = card.querySelector(".progress-chart-pins");
        var svg = card.querySelector(".progress-chart");
        if (!wrap || !tooltip || !pins || !svg) return;
        var metrics = (card.getAttribute("data-progress-metrics") || "total")
          .split(",")
          .map(function (part) { return part.trim(); })
          .filter(Boolean);
        var hits = Array.prototype.slice.call(card.querySelectorAll(".progress-chart-hit"));
        if (!hits.length) return;
        var pinnedBoxes = [];

        // The preview lives and dies with the pointer. Anything worth reading or
        // clicking gets pinned below the chart, where nothing moves it.
        function showPreview(hit, event) {
          tooltip.innerHTML = dayBoxes(hit, metrics).map(function (box) {
            return '<div class="progress-chart-panel">' + box + "</div>";
          }).join("");
          tooltip.hidden = false;
          card.classList.add("is-hovering");
          hits.forEach(function (node) {
            node.classList.toggle("is-active", node === hit);
          });
          positionTooltip(wrap, tooltip, hit, event);
        }

        function hidePreview() {
          tooltip.hidden = true;
          card.classList.remove("is-hovering");
          hits.forEach(function (node) { node.classList.remove("is-active"); });
        }

        function boxesFor(hit) {
          return pinnedBoxes.filter(function (entry) { return entry.hit === hit; });
        }

        function dropBox(entry) {
          entry.panel.remove();
          pinnedBoxes = pinnedBoxes.filter(function (candidate) { return candidate !== entry; });
          if (!boxesFor(entry.hit).length) entry.hit.classList.remove("is-pinned");
          pins.hidden = !pinnedBoxes.length;
        }

        function unpin(hit) {
          boxesFor(hit).forEach(dropBox);
        }

        function pin(hit) {
          var order = hits.indexOf(hit);
          var date = hit.getAttribute("data-date") || "day";
          dayBoxes(hit, metrics).forEach(function (box, slot) {
            var panel = document.createElement("div");
            var entry = { hit: hit, order: order, slot: slot, panel: panel };
            panel.className = "progress-chart-pin progress-chart-panel";
            panel.innerHTML =
              '<button class="progress-chart-pin-close" type="button" aria-label="Unpin ' +
              escapeHtml(date) + '">&times;</button>' + box;
            panel.querySelector(".progress-chart-pin-close").addEventListener("click", function () {
              dropBox(entry);
            });
            // Keep pinned boxes in chart order, whichever order they were clicked in.
            var later = pinnedBoxes.filter(function (candidate) {
              return candidate.order > order || (candidate.order === order && candidate.slot > slot);
            })[0];
            pins.insertBefore(panel, later ? later.panel : null);
            pinnedBoxes = pinnedBoxes.concat([entry]).sort(function (left, right) {
              return left.order - right.order || left.slot - right.slot;
            });
          });
          hit.classList.add("is-pinned");
          pins.hidden = false;
        }

        function togglePin(hit) {
          if (boxesFor(hit).length) unpin(hit);
          else pin(hit);
        }

        hits.forEach(function (hit) {
          hit.addEventListener("mouseenter", function (event) { showPreview(hit, event); });
          hit.addEventListener("mousemove", function (event) {
            if (tooltip.hidden || !hit.classList.contains("is-active")) {
              showPreview(hit, event);
              return;
            }
            positionTooltip(wrap, tooltip, hit, event);
          });
          hit.addEventListener("focus", function () { showPreview(hit, null); });
          hit.addEventListener("click", function () { togglePin(hit); });
          hit.addEventListener("keydown", function (event) {
            if (event.key !== "Enter" && event.key !== " ") return;
            event.preventDefault();
            togglePin(hit);
          });
        });
        svg.addEventListener("mouseleave", hidePreview);
        card.addEventListener("focusout", function (event) {
          if (!card.contains(event.relatedTarget)) hidePreview();
        });
        document.addEventListener("keydown", function (event) {
          if (event.key !== "Escape") return;
          hidePreview();
          pinnedBoxes.slice().forEach(dropBox);
        });
      }

      document.querySelectorAll(".progress-chart-card").forEach(bindCard);
    })();
  </script>
</body>
</html>
HTML

test -f "$site_root/Continuous-Key-Agreement/index.html"