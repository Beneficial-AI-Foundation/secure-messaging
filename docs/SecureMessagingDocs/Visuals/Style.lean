/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

/-!
# Documentation Styling

All custom CSS and the assembled render configuration for the site. Editing the
look of the docs (column width, Lean code frames, syntax-highlight palette,
game/oracle boxes) happens here and nowhere else.
-/

open Verso.Genre Manual

/-- Custom CSS injected into every page: wider content column, framed and
syntax-highlighted Lean code blocks, and the game/oracle boxes
(see `SecureMessagingDocs.Visuals.GameBoxes` for the block extensions that emit them). -/
def smDocsCss : String := r#"
/* Main content column width (centred). Tuned for oracle grids + Lean anchors. */
:root { --verso-content-max-width: calc(74rem - 2cm); }

/* Hide the blueprint panel's own collapsible code box: we already show the
   full source via the `anchor` block. */
.bp_code_panel_wrapper { display: none !important; }


/* Clearer Lean syntax highlighting palette (GitHub-light style) */
.hl.lean .keyword { color: #cf222e; }
.hl.lean .const   { color: #6639ba; }
.hl.lean .sort    { color: #0550ae; }
.hl.lean .literal { color: #0550ae; }
.hl.lean .doc-comment,
.hl.lean .comment { color: #6a737d; font-style: italic; }

/* Framed Lean code blocks (skip the one-line signatures inside blueprint panels) */
.hl.lean.block:not(.bp_external_decl_signature) {
  display: block;
  margin: 1rem 0;
  padding: 0.95rem 1.15rem;
  line-height: 1.85;
  background: #f6f8fa;
  border: 1px solid #d0d7de;
  border-radius: 8px;
  box-shadow: 0 1px 2px rgba(27, 31, 36, 0.06);
  overflow-x: auto;
}

/* Game/oracle boxes (see SecureMessagingDocs.Visuals.GameBoxes).
   The grid lays the cells out two-up. */
.game-grid {
  display: grid;
  grid-template-columns: repeat(2, minmax(0, 1fr));
  gap: 0.85rem 1rem;
  align-items: start;
  margin: 1rem 0;
}

/* Let cells shrink instead of overflowing the grid track. */
.game-grid > * {
  min-width: 0;
}

/* A single titled box (header + body). */
.game-cell {
  overflow: hidden;
  border: 1px solid #334155;
  border-radius: 4px;
  background: #ffffff;
}

/* All boxes span the full grid width (one per line). */
.game-cell[data-kind="game"],
.game-cell[data-kind="security"],
.game-cell[data-kind="oracle"],
.game-cell[data-kind="challenge"],
.game-cell[data-kind="corrupt"] {
  grid-column: 1 / -1;
}

/* The cell's title bar: experiment/oracle name (math) on the left, the state
   slice it touches on the right. One uniform colour/font for every box. */
.game-cell-header {
  display: flex;
  justify-content: space-between;
  align-items: baseline;
  gap: 1rem;
  padding: 0.45rem 0.7rem;
  border-bottom: 1px solid currentColor;
  background: #e8eefc;
  color: #1f2937;
  font-weight: 700;
  line-height: 1.25;
}
/* The right-hand state slice is lighter than the name. */
.game-cell-header > code.bp_math {
  font-weight: 400;
  font-size: 0.85em;
  opacity: 0.8;
}

/* The cell's body, holding the pseudocode math lines. */
.game-cell-body {
  padding: 0.65rem 0.75rem;
}

.game-cell-body p {
  margin: 0.18rem 0;
}

.game-cell-body .bp_math.inline {
  white-space: normal;
}

/* Left-align the pseudocode math (KaTeX centres display math by default). */
.game-grid .katex-display {
  margin: 0;
  text-align: left;
}

.game-grid .katex-display > .katex {
  text-align: left;
  white-space: normal;
}

.game-grid .bp_math.display {
  overflow-x: visible;
}

/* Informative names shown next to each definition/theorem number.
   Verso's blueprint title row is a 2-column grid (caption + number); we add a
   third column so the name sits inline on the same line, in the heading font. */
.bp_heading_title_row.bp_heading_title_row_statement {
  grid-template-columns: 11ch max-content max-content;
}
.bp-heading-title-marker {
  display: none;
}
.bp-heading-display-title {
  font: inherit;
  font-style: normal;
  font-weight: inherit;
  color: inherit;
}
/* Label introducing a node's dependency list, emitted by the `{usesLabel}`
   role. Matches the "used by" chip font in the blueprint heading. */
.uses-label {
  font-size: 0.78rem;
  font-weight: 600;
  font-style: normal;
  color: var(--bp-color-text-muted);
}

/* Tone down the dependency hyperlinks ("uses Definition …") to a sombre slate,
   with a faint underline; darken slightly on hover. */
.bp_inline_preview_ref a {
  color: #556070;
  font-style: normal;
  text-decoration-color: rgba(85, 96, 112, 0.35);
  text-underline-offset: 0.15em;
}
.bp_inline_preview_ref a:hover {
  color: #1f2937;
  text-decoration-color: currentColor;
}

.bp_used_by_target,
.bp_used_by_target_title,
.bp_used_by_target_meta,
.bp_used_by_target_meta code,
.bp_used_by_axis_badge,
.bp_used_by_preview_label,
.bp_used_by_preview_title {
  font-style: normal;
}

/* Blueprint's default theorem style adds a left rail that definitions do not
   have. Keep definitions and theorems visually uniform; the heading already
   identifies the atom kind. */
.bp_kind_theorem_content,
div.theorem_thmcontent,
html[data-bp-style="blueprint"] .bp_kind_theorem_content,
html[data-bp-style="blueprint"] div.theorem_thmcontent,
html[data-bp-style="modern"] .bp_kind_theorem_content,
html[data-bp-style="modern"] .bp_wrapper div.theorem_thmcontent,
html[data-bp-style="bold"] .bp_kind_theorem_content,
html[data-bp-style="bold"] .bp_wrapper div.theorem_thmcontent {
  border-left: 0 !important;
  padding-left: 0 !important;
}

.split-blueprint-use {
  color: #556070;
  font-style: normal;
  text-decoration-color: rgba(85, 96, 112, 0.35);
  text-underline-offset: 0.15em;
}
.split-blueprint-use:hover {
  color: #1f2937;
  text-decoration-color: currentColor;
}

/* Hidden marker before an anchor; JS moves its text into .lean-pill-caption on the row. */
p.lean-pill-caption {
  display: none;
}

/* Lean pill + optional continuation text (fixed header row; code panel below). */
.lean-anchor-row {
  margin: 1rem 0;
}
.lean-anchor-head {
  display: flex;
  align-items: baseline;
  flex-wrap: nowrap;
  gap: 0.65rem;
}
.lean-pill-caption {
  font-size: 0.9rem;
  font-style: normal;
  line-height: 1.45;
  color: #57606a;
}
.lean-anchor-body > .hl.lean.block {
  margin-top: 0;
}
.lean-anchor-body:not([hidden]) {
  margin-top: 0.45rem;
}

/* Shared pill appearance (details summary or standalone toggle button). */
.lean-pill-btn,
.lean-details > summary {
  cursor: pointer;
  display: inline-block;
  margin: 0;
  padding: 0.12rem 0.55rem;
  font-size: 0.78rem;
  font-weight: 600;
  font-style: normal;
  font-family: inherit;
  line-height: inherit;
  color: #57606a;
  background: #f6f8fa;
  border: 1px solid #d0d7de;
  border-radius: 6px;
  user-select: none;
}
.lean-pill-btn {
  appearance: none;
  -webkit-appearance: none;
}

/* Collapsible wrapper when there is no caption (added by `smDocsJs`). */
.lean-details {
  margin: 1rem 0;
}
.lean-details[open] > summary {
  margin-bottom: 0.45rem;
}
.lean-details > .hl.lean.block {
  margin-top: 0;
}

/* Standalone Lean status marker for atoms that do not yet have an anchor block. */
.lean-pill-status {
  display: flex;
  align-items: baseline;
  gap: 0.65rem;
  margin: 0.85rem 0 1rem;
  color: #57606a;
}
.lean-pill-status-label {
  display: inline-block;
  padding: 0.12rem 0.55rem;
  font-size: 0.78rem;
  font-weight: 600;
  font-style: normal;
  line-height: inherit;
  color: #57606a;
  background: #f6f8fa;
  border: 1px solid #d0d7de;
  border-radius: 6px;
}
.lean-pill-status[data-status="missing"] .lean-pill-status-label {
  color: #6f4d00;
  background: #fff7d6;
  border-color: #d9b84f;
}
.lean-pill-status[data-status="partial"] .lean-pill-status-label {
  color: #5a3e85;
  background: #f3e8ff;
  border-color: #d8b4fe;
}
.lean-pill-status[data-status="planned"] .lean-pill-status-label {
  color: #1f5f75;
  background: #e6f6fb;
  border-color: #9bd8eb;
}
.lean-pill-status-caption {
  font-size: 0.9rem;
  font-style: normal;
  line-height: 1.45;
}

.github-issue-link {
  color: #556070;
  text-decoration-color: rgba(85, 96, 112, 0.35);
  text-underline-offset: 0.15em;
  font-weight: 500;
}
.github-issue-link:hover {
  color: #1f2937;
  text-decoration-color: currentColor;
}
"#

/-- Client-side script: wrap framed anchor code in a "Lean" collapsible pill; optional
text from a preceding leanPillCaption block is shown inline after the pill. -/
def smDocsJs : String := r#"
(function () {
  function installHeadingTitles() {
    document.querySelectorAll(".bp-heading-title-marker").forEach(function (marker) {
      var label = marker.getAttribute("data-label");
      var title = marker.getAttribute("data-title");
      if (!label || !title) {
        marker.remove();
        return;
      }
      var wrapper = document.querySelector('[title="' + CSS.escape(label) + '"]');
      var row = wrapper && wrapper.querySelector(".bp_heading .bp_heading_title_row_statement");
      if (row && !row.querySelector(".bp-heading-display-title")) {
        var titleSpan = document.createElement("span");
        titleSpan.className = "bp-heading-display-title";
        titleSpan.textContent = title;
        row.appendChild(titleSpan);
      }
      marker.remove();
    });
  }
  function pillSuffixFor(code) {
    var node = code.previousElementSibling;
    while (node) {
      if (node.classList && node.classList.contains("lean-pill-caption")) {
        var html = (node.innerHTML || "").trim();
        node.remove();
        return html || null;
      }
      node = node.previousElementSibling;
    }
    return null;
  }
  function renderMathIn(root) {
    if (window.bpPreviewUtils && typeof window.bpPreviewUtils.renderMath === "function") {
      window.bpPreviewUtils.renderMath(root);
    }
  }
  function wrapLeanBlocks() {
    var blocks = document.querySelectorAll(
      "code.hl.lean.block:not(.bp_external_decl_signature):not(.lean-wrapped)");
    blocks.forEach(function (code) {
      code.classList.add("lean-wrapped");
      var suffix = pillSuffixFor(code);
      var parent = code.parentNode;
      if (suffix) {
        var row = document.createElement("div");
        row.className = "lean-anchor-row";
        var head = document.createElement("div");
        head.className = "lean-anchor-head";
        var btn = document.createElement("button");
        btn.type = "button";
        btn.className = "lean-pill-btn";
        btn.setAttribute("aria-expanded", "false");
        btn.textContent = "Lean";
        var body = document.createElement("div");
        body.className = "lean-anchor-body";
        body.hidden = true;
        var note = document.createElement("span");
        note.className = "lean-pill-caption";
        note.innerHTML = suffix;
        parent.insertBefore(row, code);
        row.appendChild(head);
        head.appendChild(btn);
        head.appendChild(note);
        row.appendChild(body);
        body.appendChild(code);
        btn.addEventListener("click", function () {
          var open = body.hidden;
          body.hidden = !open;
          btn.setAttribute("aria-expanded", open ? "true" : "false");
        });
      } else {
        var details = document.createElement("details");
        details.className = "lean-details";
        var summary = document.createElement("summary");
        summary.textContent = "Lean";
        parent.insertBefore(details, code);
        details.appendChild(summary);
        details.appendChild(code);
      }
    });
  }
  function initLeanPills() {
    installHeadingTitles();
    wrapLeanBlocks();
    window.setTimeout(function () {
      renderMathIn(document.body);
    }, 0);
  }
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initLeanPills);
  } else {
    initLeanPills();
  }
})();
"#

def smDocsAssets : HtmlAssets :=
  { extraCss := [smDocsCss], extraJs := [smDocsJs] }

/-- The site render configuration, with our custom CSS assets attached. -/
def docsConfig : RenderConfig :=
  let cfg : RenderConfig := {}
  let htmlConfig := cfg.toHtmlConfig
  { cfg with
    toHtmlConfig :=
      { htmlConfig with toHtmlAssets := htmlConfig.toHtmlAssets.combine smDocsAssets } }
