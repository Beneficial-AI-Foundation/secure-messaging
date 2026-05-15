/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Contents

/-!
# SecureMessaging Docs Renderer

Verso renderer entry point for the SecureMessaging documentation site.
-/

open Verso.Genre Manual
open Informal

def smDocsCss : CSS := CSS.mk
r#"
:root {
  --verso-code-keyword-color: #D73A49;
  --verso-code-keyword-weight: normal;
}

.hl.lean .keyword { color: #D73A49; }
.hl.lean .var { color: #24292E; }
.hl.lean .const { color: #6F42C1; }
.hl.lean .sort { color: #005CC5; }
.hl.lean .literal { color: #005CC5; }
.hl.lean .string { color: #032F62; }
.hl.lean .unknown { color: #24292E; }
.hl.lean .inter-text { color: #24292E; }

.bp_external_decl_body .docstring {
  font-family: var(--verso-text-font-family, sans-serif);
  font-size: 0.95em;
  line-height: 1.5;
  white-space: normal;
  padding: 0.6rem 0.8rem;
  margin: 0.4rem 0 0 0;
  background: #f8fafc;
  border-left: 3px solid #2563eb;
  border-radius: 0 4px 4px 0;
}

.katex-display {
  max-width: 100%;
  overflow-x: auto;
  overflow-y: hidden;
  padding: 0.15rem 0;
}

.bp_math.display {
  display: block;
  max-width: 100%;
  overflow-x: auto;
}

.sm-game-grid {
  display: grid;
  grid-template-columns: repeat(2, minmax(0, 1fr));
  gap: 0.85rem 1rem;
  align-items: start;
  margin: 1rem 0;
}

.sm-game-grid > * {
  min-width: 0;
}

.sm-game-cell {
  overflow: hidden;
  border: 1px solid #334155;
  border-radius: 4px;
  background: #ffffff;
}

.sm-game-cell[data-kind="game"],
.sm-game-cell[data-kind="challenge"],
.sm-game-cell[data-kind="security"] {
  grid-column: 1 / -1;
}

.sm-game-cell-header {
  padding: 0.45rem 0.7rem;
  border-bottom: 1px solid currentColor;
  background: #e8eefc;
  color: #1f2937;
  font-weight: 700;
  line-height: 1.25;
}

.sm-game-cell[data-kind="oracle"] {
  border-color: #3f7a5a;
}

.sm-game-cell[data-kind="oracle"] .sm-game-cell-header {
  background: #edf6f0;
  color: #3f7a5a;
}

.sm-game-cell[data-kind="challenge"] {
  border-color: #2563eb;
}

.sm-game-cell[data-kind="challenge"] .sm-game-cell-header {
  background: #eaf1ff;
  color: #2563eb;
}

.sm-game-cell[data-kind="corrupt"] {
  border-color: #dc2626;
}

.sm-game-cell[data-kind="corrupt"] .sm-game-cell-header {
  background: #fdecec;
  color: #dc2626;
}

.sm-game-cell[data-kind="security"] {
  border-color: #64748b;
}

.sm-game-cell-body {
  padding: 0.65rem 0.75rem;
}

.sm-game-cell-body p {
  margin: 0.18rem 0;
}

.sm-game-cell-body .bp_math.inline {
  white-space: normal;
}

.sm-game-grid .katex-display,
.sm-msc .katex-display {
  margin: 0;
  text-align: left;
}

.sm-game-grid .katex-display > .katex,
.sm-msc .katex-display > .katex {
  text-align: left;
  white-space: normal;
}

.sm-game-grid .bp_math.display,
.sm-msc .bp_math.display {
  overflow-x: visible;
}

.sm-msc {
  margin: 1rem 0;
  max-width: 100%;
  overflow-x: auto;
}

.sm-msc .katex-display .katex {
  font-size: 0.95em;
}

.sm-fm-diagram {
  margin: 1.2rem 0 1.5rem;
  padding: 0;
}

.sm-fm-caption {
  margin: 0 0 0.65rem;
  color: #1e293b;
  font-weight: 700;
  line-height: 1.35;
}

.sm-fm-panel {
  margin: 0.75rem 0;
  padding: 0.85rem;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #ffffff;
}

.sm-fm-panel-title {
  margin-bottom: 0.7rem;
  color: #334155;
  font-size: 0.82rem;
  font-weight: 700;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.sm-fm-roll-grid,
.sm-fm-bind-grid,
.sm-fm-flow {
  display: grid;
  gap: 0.85rem;
  align-items: center;
}

.sm-fm-roll-grid {
  grid-template-columns: minmax(0, 1.45fr) minmax(15rem, 0.75fr);
}

.sm-fm-bind-grid {
  grid-template-columns: minmax(0, 1fr) minmax(6.5rem, 0.35fr) minmax(0, 1fr);
}

.sm-fm-flow {
  grid-template-columns: minmax(0, 1fr) minmax(6.5rem, 0.48fr) minmax(0, 1fr) minmax(6.5rem, 0.48fr) minmax(0, 1fr);
}

.sm-fm-roll-tree,
.sm-fm-small-tree {
  min-width: 0;
}

.sm-fm-roll-root,
.sm-fm-tree-root {
  display: flex;
  justify-content: center;
}

.sm-fm-branches,
.sm-fm-tree-branches {
  position: relative;
  display: grid;
  gap: 0.6rem;
  margin-top: 0.85rem;
  padding-top: 1.05rem;
}

.sm-fm-three-branches {
  grid-template-columns: repeat(3, minmax(0, 1fr));
}

.sm-fm-tree-branches {
  grid-template-columns: repeat(2, minmax(0, 1fr));
}

.sm-fm-branches::before,
.sm-fm-tree-branches::before {
  content: "";
  position: absolute;
  top: 0.3rem;
  left: 12%;
  right: 12%;
  border-top: 2px solid #94a3b8;
}

.sm-fm-branch {
  position: relative;
  min-width: 0;
  padding-top: 0.7rem;
  text-align: center;
}

.sm-fm-branch::before {
  content: "";
  position: absolute;
  top: -0.25rem;
  left: 50%;
  height: 0.8rem;
  border-left: 2px solid #94a3b8;
}

.sm-fm-edge-label {
  display: inline-block;
  position: relative;
  z-index: 1;
  margin-bottom: 0.35rem;
  padding: 0.05rem 0.3rem;
  border: 1px solid #d8dee8;
  border-radius: 999px;
  background: #ffffff;
  color: #475569;
  font-size: 0.78rem;
  line-height: 1.2;
}

.sm-fm-node {
  display: inline-flex;
  min-width: 7.4rem;
  max-width: 100%;
  min-height: 3.1rem;
  flex-direction: column;
  justify-content: center;
  gap: 0.2rem;
  padding: 0.45rem 0.55rem;
  border: 1px solid #cbd5e1;
  border-radius: 5px;
  background: #f8fafc;
  color: #1f2937;
  line-height: 1.25;
  text-align: center;
}

.sm-fm-query {
  border-color: #2563eb;
  background: #eff6ff;
}

.sm-fm-subtree {
  border-style: dashed;
  border-color: #64748b;
  background: #f8fafc;
}

.sm-fm-semantic {
  border-color: #c2410c;
  background: #fff7ed;
}

.sm-fm-node-title {
  display: block;
  font-weight: 700;
}

.sm-fm-node-body {
  display: block;
  color: #475569;
  font-size: 0.78rem;
}

.sm-fm-note {
  min-width: 0;
  padding: 0.7rem 0.75rem;
  border-left: 3px solid #0f766e;
  border-radius: 0 4px 4px 0;
  background: #f0fdfa;
  color: #1f2937;
  font-size: 0.9rem;
  line-height: 1.5;
}

.sm-fm-note p {
  margin: 0.35rem 0 0;
}

.sm-fm-note-line {
  margin: 0.1rem 0;
}

.sm-fm-side-title {
  margin-bottom: 0.45rem;
  text-align: center;
}

.sm-fm-bind-arrow,
.sm-fm-flow-arrow {
  display: flex;
  min-width: 0;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 0.25rem;
  color: #7f1d1d;
  font-size: 0.78rem;
  font-weight: 700;
  line-height: 1.25;
  text-align: center;
}

.sm-fm-arrow-line,
.sm-fm-flow-arrow::after {
  display: block;
  width: 100%;
  max-width: 7rem;
  color: #b91c1c;
  font-family: monospace;
  font-size: 1rem;
}

.sm-fm-flow-arrow::after {
  content: "->";
}

.sm-fm-wide-note {
  margin-top: 0.75rem;
}

.sm-fm-diagram code {
  overflow-wrap: anywhere;
}

@media (max-width: 900px) {
  .sm-game-grid {
    grid-template-columns: minmax(0, 1fr);
  }

  .sm-fm-roll-grid,
  .sm-fm-bind-grid,
  .sm-fm-flow {
    grid-template-columns: minmax(0, 1fr);
  }

  .sm-fm-bind-arrow,
  .sm-fm-flow-arrow {
    min-height: 2rem;
  }

  .sm-fm-flow-arrow::after {
    width: auto;
  }
}

.bp_name {
  font-weight: bold;
  font-style: italic;
  white-space: nowrap;
}

.bp_heading_title_row_statement {
  display: inline-flex !important;
  align-items: baseline;
  gap: 0.35rem;
  white-space: nowrap;
}

.sm-triptych {
  margin: 1.25rem 0 1.5rem;
}

.sm-triptych-title {
  margin: 0 0 0.75rem;
  font-size: 1.05rem;
  line-height: 1.35;
  letter-spacing: 0;
}

.sm-triptych-grid {
  display: grid;
  grid-template-columns: minmax(0, 1fr);
  gap: 0.85rem;
  align-items: start;
}

.sm-triptych-panel {
  min-width: 0;
  padding: 0.85rem 0.9rem;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #ffffff;
}

.sm-triptych-paper {
  border-top: 3px solid #0f766e;
}

.sm-triptych-lean {
  border-top: 3px solid #2563eb;
}

.sm-triptych-meaning {
  border-top: 3px solid #7c3aed;
}

.sm-triptych-panel-title {
  margin: 0 0 0.55rem;
  color: #334155;
  font-size: 0.78rem;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.sm-triptych-panel-body > :first-child {
  margin-top: 0;
}

.sm-triptych-panel-body > :last-child {
  margin-bottom: 0;
}

.sm-triptych pre,
.sm-lean-source-code,
.sm-lean-source-rendered pre {
  max-width: 100%;
  white-space: pre-wrap;
  overflow-x: auto;
  overflow-wrap: anywhere;
}

.bp_external_decl_rendered pre {
  max-width: 100%;
  white-space: pre;
  overflow-x: auto;
  overflow-wrap: normal;
}

.sm-lean-detail {
  margin-top: 0.8rem;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #f8fafc;
}

.sm-lean-detail-summary {
  cursor: pointer;
  padding: 0.55rem 0.7rem;
  font-weight: 600;
  color: #1e293b;
}

.sm-lean-detail-inner {
  padding: 0 0.7rem 0.7rem;
}

.sm-lean-detail-heading {
  margin: 0.65rem 0 0.35rem;
  color: #475569;
  font-size: 0.78rem;
  font-weight: 700;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.sm-lean-source {
  margin-top: 0.35rem;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #ffffff;
}

.sm-lean-source-summary {
  padding: 0.55rem 0.7rem;
  color: #334155;
  font-size: 0.82rem;
  font-weight: 700;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.sm-lean-source-rendered {
  border-top: 1px solid #e2e8f0;
}

.sm-lean-source-rendered .examples {
  margin: 0;
  border: 0;
  border-left: 3px solid #2563eb;
  border-radius: 0 0 6px 6px;
  background: #f8fafc;
}

.sm-lean-source-rendered code.hl.lean.block {
  display: block;
  max-width: 100%;
  margin: 0;
  padding: 0.75rem 0.85rem;
  color: #24292E;
  background: #f8fafc;
  border: 0;
  border-left: 3px solid #2563eb;
  border-radius: 0 0 6px 6px;
  overflow-x: auto;
  overflow-wrap: anywhere;
  white-space: pre-wrap;
  font-family: monospace;
  font-size: 0.86em;
  line-height: 1.55;
}

.sm-lean-source-code {
  margin: 0;
  padding: 0.75rem 0.85rem;
  color: #24292E;
  background: #f8fafc;
  border: 0;
  border-left: 3px solid #2563eb;
  border-radius: 0 0 6px 6px;
  font-family: monospace;
  font-size: 0.86em;
  line-height: 1.55;
}

.bp_external_decl_rendered {
  max-width: 100%;
  overflow-x: auto;
  overflow-y: visible;
}

.bp_external_decl_rendered .bp_external_decl_body {
  overflow-wrap: anywhere;
}

.bp_code_panel_wrapper {
  display: none !important;
}

.tippy-box[data-theme~='lean'] .hover-info {
  display: block !important;
  position: static !important;
  transform: none !important;
  background: transparent !important;
  border: 0 !important;
  padding: 0 !important;
}

.tippy-box[data-theme~='lean'] .hover-info code {
  display: block;
  white-space: pre-wrap;
}
"#

def smDocsJs : JS := JS.mk
r#"
(function() {
  function onReady(fn) {
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', fn);
    } else {
      fn();
    }
  }

  onReady(function() {
    document.querySelectorAll('.bp_heading_title_row_statement').forEach(function(row) {
      if (row.querySelector('.bp_name')) return;
      var caption = row.querySelector('.bp_caption[title]');
      if (!caption) return;
      var name = caption.getAttribute('title');
      if (!name || name.length === 0) return;
      var nameSpan = document.createElement('span');
      nameSpan.className = 'bp_name';
      nameSpan.textContent = '(' + name + ')';
      row.appendChild(nameSpan);
    });
  });

  onReady(function() {
    document.documentElement.setAttribute('data-bp-style', 'modern');
  });

  onReady(function() {
    document.querySelectorAll('.sm-lean-source-rendered code.hl.lean.block').forEach(function(code) {
      if (code.dataset.smSourceTrimmed) return;
      var nodes = Array.prototype.slice.call(code.childNodes);
      var sourceStart = -1;
      for (var i = 0; i < nodes.length; i++) {
        var node = nodes[i];
        if (node.nodeType === Node.ELEMENT_NODE &&
            node.classList.contains('keyword') &&
            /^(private|noncomputable|def|abbrev|structure|inductive)$/.test(node.textContent.trim())) {
          sourceStart = i;
          break;
        }
      }
      if (sourceStart > 0) {
        for (var j = 0; j < sourceStart; j++) nodes[j].remove();
      }

      nodes = Array.prototype.slice.call(code.childNodes);
      var sourceEnd = -1;
      for (var k = nodes.length - 1; k >= 0; k--) {
        var endNode = nodes[k];
        if (endNode.nodeType === Node.ELEMENT_NODE &&
            endNode.classList.contains('keyword') &&
            endNode.textContent.trim() === 'end') {
          sourceEnd = k;
          break;
        }
      }
      if (sourceEnd >= 0) {
        for (var l = sourceEnd; l < nodes.length; l++) nodes[l].remove();
      }
      code.dataset.smSourceTrimmed = 'true';
    });
  });

  onReady(function() {
    document.querySelectorAll('.bp_code_panel_wrapper').forEach(function(panel) {
      var block = panel.previousElementSibling;
      while (block && !(block.classList && block.classList.contains('bp_wrapper'))) {
        block = block.previousElementSibling;
      }
      if (!block) return;
      if (!block.querySelector('.sm-triptych')) return;
      panel.classList.add('sm-triptych-blueprint-panel');
    });
  });
})();
"#

def main (args : List String) : IO UInt32 :=
  PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc SecureMessagingDocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := {
      toHtmlAssets := {
        features := .all
        extraCss := .ofList [smDocsCss]
        extraJs := .ofList [smDocsJs]
      }
    })
