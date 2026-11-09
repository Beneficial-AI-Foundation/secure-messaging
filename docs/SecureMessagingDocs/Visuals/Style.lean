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
:root { --verso-content-max-width: calc(74rem + 2cm); }

/* VersoBlueprint injects a Style/blueprint/modern/bold dropdown. We pick the
   look in this file, so hide the runtime switcher. */
#bp-style-switcher { display: none !important; }

/* Hide the blueprint panel's own collapsible code box: we already show the
   full source via `anchor` blocks or external-code pills (see `smDocsJs`). */
.bp_code_panel_wrapper { display: none !important; }

/* A display formula wider than its block scrolls inside the block. */
.bp_math.display {
  display: block;
  max-width: 100%;
  overflow-x: auto;
}


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

.game-cell[data-kind^="compact"] {
  grid-column: auto;
}

/* A grid with `compact-third` cells puts them in one row, each as wide as its
   content needs. A cell that does not fit wraps to the next row. */
.game-grid:has(> .game-cell[data-kind="compact-third"]) {
  display: flex;
  flex-wrap: wrap;
}

.game-grid > .game-cell[data-kind="compact-third"] {
  flex: 1 1 auto;
}

.game-grid:has(> .game-cell[data-kind="compact-third"]) > :not(.game-cell) {
  flex-basis: 100%;
}

/* Other blocks in a grid, such as a Lean pill, span the full width. */
.game-grid > :not(.game-cell) {
  grid-column: 1 / -1;
}

.game-cell[data-kind^="compact"] .game-cell-body,
.game-cell[data-kind^="compact"] .game-cell-header {
  font-size: 0.92em;
}

.game-cell[data-kind="compact-send"] {
  order: 1;
}

.game-cell[data-kind="compact-recv"] {
  order: 2;
}

@media (max-width: 640px) {
  .game-grid {
    grid-template-columns: 1fr;
  }

  .game-cell[data-kind^="compact"] {
    grid-column: 1 / -1;
  }
}

/* The cell's title bar: experiment/oracle name (math) on the left, the state
   slice it touches on the right. One uniform colour/font for every box.
   Doubles as the fold/unfold toggle (see `smDocsJs`): clicking it shows/hides
   the body. */
.game-cell-header {
  display: flex;
  justify-content: flex-start;
  align-items: baseline;
  gap: 0.6rem;
  padding: 0.45rem 0.7rem;
  border-bottom: 1px solid currentColor;
  background: #e8eefc;
  color: #1f2937;
  font-weight: 700;
  line-height: 1.25;
}
/* Foldable boxes: header is interactive; drop the separator when folded so the
   collapsed box reads as a single bar. */
.game-foldable .game-cell-header {
  cursor: pointer;
  user-select: none;
}
.game-foldable:not(.is-open) .game-cell-header {
  border-bottom: 0;
}
/* Fold indicator: a caret that points right when folded and down when open. */
.game-cell-caret {
  flex: none;
  align-self: center;
  font-size: 0.85em;
  line-height: 1;
  opacity: 0.7;
  transform: rotate(-90deg);
  transition: transform 0.15s ease;
}
.game-foldable.is-open .game-cell-caret {
  transform: rotate(0deg);
}
/* The right-hand state slice is lighter than the name and sits at the far end. */
.game-cell-header > code.bp_math {
  font-weight: 400;
  font-size: 0.85em;
  opacity: 0.8;
  margin-left: auto;
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

/* Scheme interfaces and game state retain paper-style typography. */
.game-cell[data-kind="scheme"],
.game-cell[data-kind="scheme-notation"],
.game-cell[data-kind="scheme-algorithms"],
.game-cell[data-kind="scheme-diagram"] {
  grid-column: 1 / -1;
}
.game-cell[data-kind^="scheme"] {
  border-radius: 0;
  font-family: "Times New Roman", Times, serif;
}
.game-cell[data-kind^="scheme"] .game-cell-body > p {
  margin: 0.8rem 0 0.3rem;
}
.game-cell[data-kind^="scheme"] .game-cell-body :is(p, li) {
  font-family: inherit;
  font-style: italic;
}
.game-cell[data-kind^="scheme"] .game-cell-body > p:first-child {
  margin-top: 0;
}
.game-cell[data-kind^="scheme"] .bp_math.display {
  display: block;
  max-width: 100%;
  overflow-x: auto;
  padding-block: 0.15rem;
}

/* Notation and explicit party algorithms use two columns when space permits. */
.game-cell:is([data-kind="scheme-notation"], [data-kind="scheme-algorithms"]) {
  container-type: inline-size;
}
.game-cell:is([data-kind="scheme-notation"], [data-kind="scheme-algorithms"]) table.tabular {
  width: 100%;
  table-layout: fixed;
  border-spacing: 0;
  margin: 0;
}
.game-cell:is([data-kind="scheme-notation"], [data-kind="scheme-algorithms"]) td {
  width: 50%;
  padding: 0 1rem 0 0;
}
.game-cell:is([data-kind="scheme-notation"], [data-kind="scheme-algorithms"]) td + td {
  padding: 0 0 0 1rem;
}
.game-cell:is([data-kind="scheme-notation"], [data-kind="scheme-algorithms"]) td > p {
  margin: 0.8rem 0 0.3rem;
}
.game-cell[data-kind="scheme-algorithms"] table.tabular {
  width: calc(100% + 1.5rem);
  margin: 1rem -0.75rem 0;
  border-spacing: 0.75rem 0;
}
.game-cell[data-kind="scheme-notation"] td > ul {
  margin: 0;
  padding-inline-start: 1.25rem;
}
@container (max-width: 46rem) {
  .game-cell:is([data-kind="scheme-notation"], [data-kind="scheme-algorithms"]) td {
    display: block;
    width: auto;
    padding: 0;
  }
  .game-cell:is([data-kind="scheme-notation"], [data-kind="scheme-algorithms"]) td + td {
    padding: 1rem 0 0;
  }
}

/* Frame each party's algorithms within the shared Algorithms box. */
.game-cell[data-kind="scheme-algorithms"] td,
.game-cell[data-kind="scheme-algorithms"] td + td {
  border: 1px solid #334155;
  padding: 0.65rem 0.75rem;
}
.game-cell[data-kind="scheme-algorithms"] td > p:first-child {
  margin-top: 0;
}
@container (max-width: 46rem) {
  .game-cell[data-kind="scheme-algorithms"] table.tabular {
    width: 100%;
    margin-inline: 0;
    border-spacing: 0;
  }
  .game-cell[data-kind="scheme-algorithms"] td + td {
    margin-top: 0.75rem;
  }
}

/* Keep the state diagram at its designed scale on wide pages. */
.diagram > svg.spqr-states {
  max-width: 1080px;
  margin-inline: auto;
}

/* These definitions pair short algorithms according to the available content width. */
:is(#--informal-preview-spqr_parameters--statement,
    #--informal-preview-spqr_chunked_scheme--statement,
    #--informal-preview-spqr_protocol_spec--statement,
    #--informal-preview-incremental_kem_det--statement) {
  container-type: inline-size;
  container-name: spqr-protocol;
}
:is(#--informal-preview-spqr_parameters--statement,
    #--informal-preview-spqr_chunked_scheme--statement,
    #--informal-preview-spqr_protocol_spec--statement,
    #--informal-preview-incremental_kem_det--statement) .game-grid {
  grid-template-columns: minmax(0, 1fr);
}
#--informal-preview-spqr_chunked_scheme--statement .game-cell,
#--informal-preview-spqr_chunked_spec--statement {
  scroll-margin-top: 4rem;
}
@container spqr-protocol (min-width: 31rem) {
  :is(#--informal-preview-spqr_parameters--statement,
      #--informal-preview-spqr_chunked_scheme--statement,
      #--informal-preview-spqr_protocol_spec--statement,
    #--informal-preview-incremental_kem_det--statement) .game-grid {
    grid-template-columns: repeat(2, minmax(0, 1fr));
  }
}
:is(#--informal-preview-spqr_parameters--statement,
    #--informal-preview-spqr_chunked_scheme--statement,
    #--informal-preview-spqr_protocol_spec--statement,
    #--informal-preview-incremental_kem_det--statement) .game-grid .game-cell-body > p {
  max-width: 100%;
  overflow-x: auto;
}
@container spqr-protocol (max-width: 48rem) {
  :is(#--informal-preview-spqr_parameters--statement,
      #--informal-preview-spqr_chunked_scheme--statement,
      #--informal-preview-spqr_protocol_spec--statement,
    #--informal-preview-incremental_kem_det--statement) .game-grid .katex {
    font-size: 1em;
  }
}
#--informal-preview-spqr_chunked_scheme--statement .game-cell-header {
  flex-wrap: wrap;
}

/* Send and Receive sit beside the helper boxes they call: the transition in the left column,
   spanning the rows of its helpers, which stack in the right column. The math takes the size of
   the narrow layout so the longest pseudocode rows fit the column. */
@container spqr-protocol (min-width: 48rem) {
  .game-grid:has(> #spqr-send),
  .game-grid:has(> #spqr-receive) {
    grid-template-columns: minmax(0, 5fr) minmax(0, 3fr);
  }
  /* The helper panel sizes to its content; a trailing flexible row takes the height the
     transition has beyond it, so the panel stays at the top. */
  .game-grid:has(> #spqr-send),
  .game-grid:has(> #spqr-receive) {
    grid-template-rows: max-content 1fr;
  }
  #spqr-send,
  #spqr-receive {
    grid-column: 1;
    grid-row: 1 / span 2;
  }
  #spqr-send ~ .game-cell,
  #spqr-receive ~ .game-cell {
    grid-column: 2;
  }
  .game-grid:has(> #spqr-send) .katex,
  .game-grid:has(> #spqr-receive) .katex {
    font-size: 1em;
  }
}

/* Keep wide tables and unbroken state names inside their own scrollers. The relative
   position also contains KaTeX's absolutely positioned MathML, which would otherwise widen the
   page when a formula starts beyond the right edge. */
#spqr-states table.tabular,
#--informal-preview-spqr_protocol_spec--statement table.tabular {
  display: block;
  position: relative;
  width: 100%;
  max-width: 100%;
  overflow-x: auto;
}
#spqr-states table.tabular :is(th, td) {
  vertical-align: top;
}
/* The epoch chart scrolls rather than widening the page on narrow windows. */
#spqr-states .katex-display {
  overflow-x: auto;
  overflow-y: hidden;
}

/* Centre the communication diagram while retaining readable math on narrow screens. */
.game-cell[data-kind="scheme-diagram"] .katex-display > .katex {
  width: max-content;
  min-width: 100%;
  text-align: center;
}

/* Errata boxes (see SecureMessagingDocs.Visuals.GameBoxes, `erratum`): a framed
   note with an amber accent, a plain-text header (number, title, scope) and a
   prose body holding math, a pseudocode excerpt, or a correction table. */
.erratum {
  margin: 1.25rem 0;
  border: 1px solid #334155;
  border-left: 5px solid #b45309;
  border-radius: 4px;
  background: #ffffff;
  overflow: hidden;
}
.erratum-header {
  display: flex;
  flex-wrap: wrap;
  align-items: baseline;
  gap: 0.3rem 0.75rem;
  padding: 0.5rem 0.85rem;
  background: #fdf3e3;
  border-bottom: 1px solid #e7cfa6;
  color: #1f2937;
  line-height: 1.3;
}
.erratum-number {
  flex: none;
  font-size: 0.8em;
  font-weight: 700;
  letter-spacing: 0.05em;
  text-transform: uppercase;
  color: #92400e;
}
.erratum-title {
  font-weight: 700;
}
.erratum-scope {
  margin-left: auto;
  font-size: 0.85em;
  color: #57606a;
}
.erratum-body {
  padding: 0.75rem 0.95rem;
}
.erratum-body > :first-child {
  margin-top: 0;
}
.erratum-body > :last-child {
  margin-bottom: 0;
}
.erratum-body p {
  margin: 0.55rem 0;
}
.erratum-body .bp_math.inline {
  white-space: normal;
}
/* Pseudocode excerpts: left-aligned display math, as in the protocol boxes. */
.erratum-body .katex-display {
  margin: 0.7rem 0 0.7rem 1rem;
  text-align: left;
}
.erratum-body .katex-display > .katex {
  text-align: left;
  white-space: normal;
}
/* Correction tables: light rules, generous column gaps, no wrapping of math. */
.erratum-body table.tabular {
  margin: 0.6rem 0 0.8rem;
  border-collapse: collapse;
}
.erratum-body table.tabular th,
.erratum-body table.tabular td {
  padding: 0.3rem 1.6rem 0.3rem 0;
  text-align: left;
  vertical-align: baseline;
  border-bottom: 1px solid #e5e7eb;
}
.erratum-body table.tabular th {
  font-weight: 600;
  border-bottom: 1px solid #334155;
}
.erratum-body table.tabular :is(th, td) > p {
  margin: 0;
}

/* Informative names shown next to each definition/theorem number.
   Verso's blueprint title row is a 2-column grid (caption + number); we add a
   third column so the name sits inline on the same line, in the heading font. */
.bp_heading_title_row.bp_heading_title_row_statement {
  grid-template-columns: 11ch max-content max-content auto;
}
/* Share link after the title: copies the URL of the definition or theorem. */
.bp-share-link {
  position: relative;
  display: inline-flex;
  align-items: center;
  align-self: center;
  justify-self: start;
  margin-inline-start: 0.35rem;
  padding: 0.12rem;
  border-radius: 4px;
  color: var(--bp-color-text-faint);
  opacity: 0.45;
  text-decoration: none;
  transition: opacity 0.15s;
}
.bp_heading:hover .bp-share-link,
.bp-share-link:focus-visible,
.bp-share-link.is-flashing {
  opacity: 1;
}
.bp-share-link:hover,
.bp-share-link:focus-visible {
  color: var(--bp-color-text-muted);
  background: var(--bp-color-surface-muted);
}
.bp-share-link.is-flashing {
  color: #2a7b7b;
}
.bp-share-link svg {
  width: 0.9rem;
  height: 0.9rem;
}
.bp-share-link[data-feedback]::after {
  content: attr(data-feedback);
  position: absolute;
  left: 50%;
  bottom: calc(100% + 4px);
  transform: translateX(-50%);
  padding: 0.15rem 0.4rem;
  border-radius: 4px;
  background: #1f2937;
  color: #fff;
  font-size: 0.72rem;
  font-weight: 600;
  white-space: nowrap;
  pointer-events: none;
}
/* The same feedback for screen readers, which do not read the tooltip. */
.bp-share-status {
  position: absolute;
  width: 1px;
  height: 1px;
  margin: -1px;
  padding: 0;
  overflow: hidden;
  clip-path: inset(50%);
  white-space: nowrap;
  border: 0;
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
/* Tone down inline node references ({bpref}, citations) to a sombre slate,
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
  font-style: normal !important;
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
.lean-anchor-body > .hl.lean.block,
.lean-anchor-body > pre {
  margin-top: 0;
}
.lean-anchor-body:not([hidden]) {
  margin-top: 0.45rem;
}

/* `leanCompare`: one pill whose panel stacks its code blocks, each full width. */
.lean-compare-body:not([hidden]) {
  display: grid;
  grid-template-columns: minmax(0, 1fr);
  gap: 0.85rem;
}
.lean-compare-col {
  min-width: 0;
}
.lean-compare-col > .hl.lean.block {
  margin: 0;
}
.lean-compare-label {
  margin-bottom: 0.3rem;
  font-size: 0.85rem;
  font-weight: 600;
  color: #57606a;
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

/* External Lean pills: teal tint on the "Lean" button for code blocks quoting
   external (VCVio) source, to set them apart from local-code anchors. */
.lean-pill-btn.lean-pill-btn-external {
  color: #0f5c4c;
  background: #e6f7f2;
  border-color: #7dceb8;
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
.bp_summary_badge .github-issue-link,
.bp_summary_badge .github-issue-link:hover {
  color: inherit;
  text-decoration-color: currentColor;
}

/* Keep issue links beside the title and use consistent text for header controls. */
.bp_header_issues + .bp_extras {
  display: flex;
  align-items: center;
  flex-wrap: wrap;
  gap: 0.2rem 0.55rem;
}
.bp_header_issues,
.bp_extras .bp_relation_chip {
  font-family: inherit;
  font-size: 0.78rem;
  font-weight: 600;
  line-height: 1.2;
}
.bp_header_issues {
  color: var(--bp-color-text-muted);
  margin-inline-start: 0.45rem;
}
.bp_header_issues .bp_metadata_tag,
.bp_header_issues .github-issue-link {
  font: inherit;
  color: inherit;
}
.bp_header_issues .bp_metadata_tag {
  border: none;
  background: none;
  padding: 0;
}
.bp_header_issues .github-issue-link {
  display: inline-flex;
  align-items: center;
  gap: 0.25rem;
  padding: 0.12rem 0.4rem;
  border: 1px solid var(--bp-color-border-panel);
  border-radius: 999px;
  background: var(--bp-color-surface);
  text-decoration: none;
}
.bp_header_issues .github-issue-link:hover,
.bp_header_issues .github-issue-link:focus-visible {
  background: var(--bp-color-surface-muted);
  border-color: var(--bp-color-text-faint);
}
.bp_issue_icon {
  width: 0.75rem;
  height: 0.75rem;
  flex: none;
}

/* Keep remaining metadata, or the fallback without a toolbar, below the body. */
.bp_wrapper > .bp_metadata_panel {
  background: transparent;
  border: none;
  padding: 0;
  margin: 0.5rem 0 0.2rem;
}

/* Hash navigation should highlight declarations, not an entire section. */
section.bp_decl_target {
  background: transparent;
  box-shadow: none;
  animation: none;
}
"#

/-- Client-side documentation UI: heading titles, issue badges, collapsible Lean blocks
and game boxes, math rendering, and fragment navigation. -/
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
      var wrapper = document.querySelector('.bp_wrapper[title="' + CSS.escape(label) + '"]');
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
    // Internal anchors and checked external quotations use the same highlighted
    // Lean block renderer.
    var blocks = document.querySelectorAll(
      "code.hl.lean.block:not(.bp_external_decl_signature):not(.lean-wrapped)");
    blocks.forEach(function (code) {
      code.classList.add("lean-wrapped");
      // `leanCompare` panels already sit under their own pill.
      if (code.closest(".lean-compare-body")) return;
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
        if (/VCVio/.test(suffix)) {
          btn.classList.add("lean-pill-btn-external");
        }
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
  function installLeanCompares() {
    document.querySelectorAll(".lean-compare > .lean-anchor-head > .lean-pill-btn")
      .forEach(function (btn) {
        var body = btn.closest(".lean-compare").querySelector(":scope > .lean-anchor-body");
        if (!body) return;
        btn.addEventListener("click", function () {
          var open = body.hidden;
          body.hidden = !open;
          btn.setAttribute("aria-expanded", open ? "true" : "false");
        });
      });
  }
  function moveMetadataPanels() {
    document.querySelectorAll(".bp_wrapper > .bp_metadata_panel").forEach(function (panel) {
      var wrapper = panel.parentNode;
      var toolbar = wrapper.querySelector(":scope > .bp_heading > .bp_extras");
      if (toolbar) {
        panel.querySelectorAll(":scope > .bp_metadata_item").forEach(function (item) {
          var key = item.querySelector(".bp_metadata_key");
          // Move only dedicated GitHub metadata; preserve other tags below the body.
          if (!key || key.textContent.trim() !== "GitHub" ||
              !item.querySelector("a.github-issue-link")) return;
          key.remove();
          item.querySelectorAll("a.github-issue-link").forEach(function (link) {
            var label = "GitHub issue " + link.textContent.trim();
            link.title = label;
            link.setAttribute("aria-label", label);
            link.insertAdjacentHTML("afterbegin",
              '<svg class="bp_issue_icon" viewBox="0 0 16 16" aria-hidden="true" focusable="false">' +
              '<circle cx="8" cy="8" r="6" fill="none" stroke="currentColor" stroke-width="1.5"/>' +
              '<circle cx="8" cy="8" r="1.5" fill="currentColor"/></svg>');
          });
          item.classList.add("bp_header_issues");
          toolbar.parentNode.insertBefore(item, toolbar);
        });
      }
      if (panel.children.length) {
        wrapper.appendChild(panel);
      } else {
        panel.remove();
      }
    });
  }
  function foldGameCells() {
    document.querySelectorAll("section.game-cell:not(.game-foldable)").forEach(function (cell) {
      var header = cell.querySelector(":scope > .game-cell-header");
      var body = cell.querySelector(":scope > .game-cell-body");
      if (!header || !body) return;
      cell.classList.add("game-foldable");
      var caret = document.createElement("span");
      caret.className = "game-cell-caret";
      caret.setAttribute("aria-hidden", "true");
      caret.textContent = "\u25BE";
      header.insertBefore(caret, header.firstChild);
      header.setAttribute("role", "button");
      header.setAttribute("tabindex", "0");
      // Cells opt into an expanded body; the default remains folded.
      var initiallyOpen = cell.getAttribute("data-open") === "true";
      body.hidden = !initiallyOpen;
      cell.classList.toggle("is-open", initiallyOpen);
      header.setAttribute("aria-expanded", initiallyOpen ? "true" : "false");
      function toggle() {
        var open = body.hidden;
        body.hidden = !open;
        cell.classList.toggle("is-open", open);
        header.setAttribute("aria-expanded", open ? "true" : "false");
      }
      header.addEventListener("click", toggle);
      header.addEventListener("keydown", function (event) {
        if (event.key === "Enter" || event.key === " " || event.key === "Spacebar") {
          event.preventDefault();
          toggle();
        }
      });
    });
  }
  // Share links: each definition or theorem heading gets an icon that copies the URL of
  // the statement, whose id is `--informal-preview-<label>--statement`.
  function statementName(wrapper) {
    var caption = wrapper.querySelector(":scope > .bp_heading .bp_caption");
    var number = wrapper.querySelector(":scope > .bp_heading .bp_label");
    var parts = [caption && caption.textContent.trim(), number && number.textContent.trim()];
    return parts.filter(Boolean).join(" ") || "this statement";
  }
  function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      return navigator.clipboard.writeText(text);
    }
    return new Promise(function (resolve, reject) {
      var area = document.createElement("textarea");
      area.value = text;
      area.setAttribute("readonly", "");
      area.style.position = "fixed";
      area.style.opacity = "0";
      document.body.appendChild(area);
      area.select();
      var copied = false;
      try { copied = document.execCommand("copy"); } catch (_) {}
      area.remove();
      if (copied) { resolve(); } else { reject(); }
    });
  }
  // A status region announces the copy feedback; screen readers do not read the tooltip.
  var shareStatus = null;
  function flashShareLink(link, text) {
    link.setAttribute("data-feedback", text);
    link.classList.add("is-flashing");
    shareStatus.textContent = text;
    window.clearTimeout(link.bpFlashTimer);
    link.bpFlashTimer = window.setTimeout(function () {
      link.classList.remove("is-flashing");
      link.removeAttribute("data-feedback");
      shareStatus.textContent = "";
    }, 1600);
  }
  function installShareLinks() {
    // Created with the links: a region added at the moment of its update is often not announced.
    if (!shareStatus) {
      shareStatus = document.createElement("div");
      shareStatus.className = "bp-share-status";
      shareStatus.setAttribute("role", "status");
      document.body.appendChild(shareStatus);
    }
    document.querySelectorAll('.bp_wrapper[id$="--statement"]').forEach(function (wrapper) {
      var row = wrapper.querySelector(":scope > .bp_heading .bp_heading_title_row_statement");
      if (!row || row.querySelector(".bp-share-link")) return;
      // An absolute URL: pages set `<base href>`, against which `#id` would name the site root.
      var url = window.location.origin + window.location.pathname + window.location.search +
        '#' + wrapper.id;
      var label = "Copy link to " + statementName(wrapper);
      var link = document.createElement("a");
      link.className = "bp-share-link";
      link.href = url;
      link.title = label;
      link.setAttribute("aria-label", label);
      link.innerHTML =
        '<svg viewBox="0 0 16 16" aria-hidden="true" focusable="false" fill="none" ' +
        'stroke="currentColor" stroke-width="1.5" stroke-linecap="round">' +
        '<path d="M6.6 9.4l2.8-2.8"/>' +
        '<path d="M7.3 4.7l1.1-1.1a2.6 2.6 0 0 1 3.7 3.7l-1.1 1.1"/>' +
        '<path d="M8.7 11.3l-1.1 1.1a2.6 2.6 0 0 1-3.7-3.7l1.1-1.1"/></svg>';
      link.addEventListener("click", function (event) {
        // Modified and middle clicks keep the default link behaviour.
        if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey ||
            event.altKey) return;
        // Keep the page in place: the blueprint's link handler would re-centre the statement.
        event.preventDefault();
        event.stopPropagation();
        window.history.replaceState(null, "", url);
        copyText(url).then(
          function () { flashShareLink(link, "Link copied"); },
          function () { flashShareLink(link, "Copy the address bar"); });
      });
      row.appendChild(link);
    });
  }
  function revealFragment() {
    var hash = window.location.hash;
    if (!hash) return;
    var target;
    try {
      var id = decodeURIComponent(hash.slice(1));
      // A short link `#<label>` names the statement `--informal-preview-<label>--statement`.
      target = document.getElementById(id) ||
        document.getElementById("--informal-preview-" + id + "--statement");
    } catch (_) {
      return;
    }
    if (!target) return;
    // Open only the disclosures containing the destination.
    for (var node = target; node; node = node.parentElement) {
      if (node.tagName === "DETAILS") node.open = true;
      if (node.classList.contains("lean-anchor-body")) {
        node.hidden = false;
        node.parentElement.querySelector(".lean-anchor-head > .lean-pill-btn")
          .setAttribute("aria-expanded", "true");
      }
      // A folded game cell: open it whether the target is the cell itself (a
      // tagged cell linked via `cellref`) or something inside its body.
      if (node.classList.contains("game-foldable")) {
        var cellBody = node.querySelector(":scope > .game-cell-body");
        if (cellBody) {
          cellBody.hidden = false;
          node.classList.add("is-open");
          node.querySelector(":scope > .game-cell-header")
            .setAttribute("aria-expanded", "true");
        }
      }
    }
    window.requestAnimationFrame(function () {
      if (window.location.hash === hash) {
        // Keep section and SPQR panel/table headings visible; declarations stay centered.
        var isSection = target.matches("h1, h2, h3, h4, h5, h6") ||
          (target.tagName === "SECTION" &&
            target.querySelector(":scope > :is(h1, h2, h3, h4, h5, h6)"));
        var isSpqrBlock = target.matches(".game-cell, table.tabular") &&
          target.closest('#--informal-preview-spqr_chunked_scheme--statement') !== null;
        target.scrollIntoView({
          block: isSection || isSpqrBlock ? "start" : "center", inline: "nearest",
          // Cancel Blueprint's concurrent smooth centering for these large targets.
          behavior: isSpqrBlock ? "instant" : "auto"
        });
      }
    });
  }
  window.addEventListener("hashchange", revealFragment);
  document.addEventListener("click", function (event) {
    if (event.defaultPrevented || event.button !== 0 || event.metaKey ||
        event.ctrlKey || event.shiftKey || event.altKey ||
        !(event.target instanceof Element)) return;
    var link = event.target.closest("a[href]");
    if (!link || link.hasAttribute("download") ||
        (link.target && link.target !== "_self")) return;
    var url = new URL(link.href, document.baseURI);
    if (url.origin !== window.location.origin ||
        url.pathname !== window.location.pathname ||
        url.search !== window.location.search || !url.hash ||
        url.hash !== window.location.hash) return;
    // Reopening the current fragment does not emit hashchange.
    window.setTimeout(function () {
      if (!event.defaultPrevented) revealFragment();
    }, 0);
  });
  function initLeanPills() {
    installHeadingTitles();
    installShareLinks();
    wrapLeanBlocks();
    installLeanCompares();
    moveMetadataPanels();
    foldGameCells();
    window.setTimeout(function () {
      renderMathIn(document.body);
      revealFragment();
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

/-- The site render configuration, with our custom CSS and JavaScript assets attached. -/
def docsConfig : RenderConfig :=
  let cfg : RenderConfig := {}
  let htmlConfig := cfg.toHtmlConfig
  { cfg with
    toHtmlConfig :=
      { htmlConfig with toHtmlAssets := htmlConfig.toHtmlAssets.combine smDocsAssets } }
