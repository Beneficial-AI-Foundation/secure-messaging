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

# Decide whether recovered history is compatible with the current tracked atom
# universe. Re-seeding avoids visual spikes when old deployed exact snapshots
# used a different counting basis.
history_reseed_reason() {
  local history_file="$1"
  python3 - "$history_file" "$site_root" "$docs_root" <<'PY'
import importlib.util
import json
import sys
from pathlib import Path

history_path = Path(sys.argv[1])
site_dir = Path(sys.argv[2])
docs_dir = Path(sys.argv[3])
expected_basis = "linked closing PR merge dates"

if not history_path.exists():
    print("missing")
    raise SystemExit

try:
    data = json.loads(history_path.read_text())
except Exception:
    print("invalid")
    raise SystemExit

snapshots = data if isinstance(data, list) else data.get("snapshots", []) if isinstance(data, dict) else []
if not isinstance(snapshots, list) or len(snapshots) < 2:
    print("sparse")
    raise SystemExit

if not isinstance(data, dict) or expected_basis not in str(data.get("historyBasis", "")):
    print("stale-basis")
    raise SystemExit

script = Path("scripts/aggregate-blueprint-status.py")
spec = importlib.util.spec_from_file_location("aggregate_blueprint_status", script)
if spec is None or spec.loader is None:
    print("invalid")
    raise SystemExit
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
totals = module.summarize(module.load_tracked_atoms(site_dir, docs_dir))
expected = {
    "definitions": totals["definition"]["total"],
    "theorems": totals["theorem"]["total"],
}
for snapshot in snapshots:
    definitions = snapshot.get("definitions", {}) if isinstance(snapshot, dict) else {}
    theorems = snapshot.get("theorems", {}) if isinstance(snapshot, dict) else {}
    if definitions.get("total") != expected["definitions"] or theorems.get("total") != expected["theorems"]:
        print("total-mismatch")
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
  "docs/SecureMessagingDocs/Renderers/FSAEADMain.lean|SecureMessagingDocs.Chapters.FSAEAD.Overview|Forward-Secure-AEAD|Forward-Secure AEAD|FS-AEAD Contents:"
  "docs/SecureMessagingDocs/Renderers/OnOffKEMMain.lean|SecureMessagingDocs.Chapters.OnOffKEM.Overview|Online-Offline-KEM|Online-Offline KEM|OO-KEM Contents:"
  "docs/SecureMessagingDocs/Renderers/PRFPRNGMain.lean|SecureMessagingDocs.Chapters.PRFPRNG.Overview|PRF-PRNG|PRF-PRNG|PRF-PRNG Contents:"
  "docs/SecureMessagingDocs/Renderers/RKEMMain.lean|SecureMessagingDocs.Chapters.RKEM.Overview|Ratcheting-KEM|Ratcheting KEM|RKEM Contents:"
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
    .status-table .proof-group {
      border-left: 1px solid var(--line);
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
      grid-template-columns: repeat(2, minmax(0, 1fr));
      gap: 16px;
    }
    .progress-chart-card {
      padding: 15px;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--panel);
      overflow-x: auto;
      scrollbar-gutter: stable;
    }
    .progress-chart-card h3 {
      margin: 0 0 10px;
      font-size: 1rem;
    }
    .progress-chart {
      display: block;
      width: 100%;
      min-width: 588px;
      height: auto;
      overflow: visible;
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
      gap: 12px;
      margin-top: 9px;
      overflow-x: auto;
      white-space: nowrap;
      color: var(--muted);
      font-size: 0.95rem;
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
    @media (max-width: 900px) {
      .progress-chart-grid {
        grid-template-columns: 1fr;
      }
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
      .progress-chart-grid {
        grid-template-columns: 1fr;
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
</body>
</html>
HTML

test -f "$site_root/Continuous-Key-Agreement/index.html"