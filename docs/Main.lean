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

.sm-cryptocode {
  margin: 1.1rem 0 1.45rem;
  max-width: 100%;
  color: #111827;
  background: #ffffff;
  font-size: 0.94rem;
  line-height: 1.38;
}

.sm-crypto-caption {
  margin: 0 0 0.65rem;
  color: #111827;
  font-weight: 700;
  line-height: 1.3;
}

.sm-crypto-flow-grid {
  display: grid;
  grid-template-columns: minmax(16rem, 1fr) minmax(12rem, 0.55fr) minmax(16rem, 1fr);
  gap: 0.35rem 0.9rem;
  align-items: center;
}

.sm-crypto-party {
  padding: 0.1rem 0 0.28rem;
  border-bottom: 1.5px solid #111827;
  font-size: 1.08rem;
  font-weight: 700;
  line-height: 1.2;
}

.sm-crypto-party-right {
  text-align: right;
}

.sm-crypto-cell {
  min-width: 0;
  padding: 0.38rem 0.05rem;
}

.sm-crypto-empty {
  min-height: 2.25rem;
}

.sm-crypto-comment {
  margin: 0.16rem 0 0.22rem;
  color: #111827;
  font-size: 0.84rem;
}

.sm-crypto-line {
  display: flex;
  flex-wrap: wrap;
  gap: 0.22rem;
  align-items: baseline;
  margin: 0.14rem 0;
}

.sm-crypto-assign {
  color: #475569;
}

.sm-crypto-chip {
  display: inline-flex;
  align-items: center;
  min-height: 1.25rem;
  padding: 0.02rem 0.35rem;
  border-radius: 0.32rem;
  color: #ffffff;
  font-weight: 700;
  line-height: 1.2;
}

.sm-crypto-chip code {
  color: inherit;
}

.sm-crypto-chip-comm {
  background: #3f7a5a;
}

.sm-crypto-chip-key {
  background: #2563eb;
}

.sm-crypto-chip-ok {
  background: #dc2626;
}

.sm-crypto-flow .sm-cka-lens {
  margin-top: 1rem;
  padding-top: 0.75rem;
  border-top: 1px solid #e5e7eb;
}

.sm-crypto-arrow {
  display: flex;
  min-width: 0;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 0.15rem;
  color: #111827;
  font-size: 0.84rem;
  font-style: italic;
  line-height: 1.2;
  text-align: center;
}

.sm-crypto-flow .sm-cka-wire-label {
  padding: 0;
  border: 0;
  background: transparent;
}

.sm-crypto-arrow .sm-cka-wire-line {
  position: relative;
  display: block;
  width: 100%;
  min-width: 7rem;
  height: 1rem;
}

.sm-crypto-arrow-right .sm-cka-wire-line::before,
.sm-crypto-arrow-left .sm-cka-wire-line::before {
  content: "";
  position: absolute;
  top: 0.48rem;
  left: 0;
  right: 0;
  border-top: 1px solid #111827;
}

.sm-crypto-arrow-right .sm-cka-wire-line::after,
.sm-crypto-arrow-left .sm-cka-wire-line::after {
  content: "";
  position: absolute;
  top: 0.28rem;
  width: 0.42rem;
  height: 0.42rem;
  border-top: 1px solid #111827;
  border-right: 1px solid #111827;
}

.sm-crypto-arrow-right .sm-cka-wire-line::after {
  right: 0;
  transform: rotate(45deg);
}

.sm-crypto-arrow-left .sm-cka-wire-line::after {
  left: 0;
  transform: rotate(225deg);
}

.sm-crypto-game-layout {
  display: grid;
  grid-template-columns: minmax(0, 1.6fr) minmax(14rem, 0.75fr);
  gap: 1.15rem;
  align-items: start;
}

.sm-crypto-game-board {
  border: 1px solid #111827;
  background: #ffffff;
}

.sm-crypto-game-titlebar {
  display: flex;
  flex-wrap: wrap;
  gap: 0.45rem 0.75rem;
  align-items: baseline;
  padding: 0.45rem 0.65rem;
  border-bottom: 1px solid #9ca3af;
  background: #e5e7eb;
}

.sm-crypto-game-main-title {
  font-weight: 700;
}

.sm-crypto-game-subtitle {
  color: #2563eb;
  font-size: 0.84rem;
  font-style: italic;
}

.sm-crypto-proc-grid {
  display: grid;
  grid-template-columns: repeat(3, minmax(0, 1fr));
  gap: 0.8rem 0.9rem;
  padding: 0.75rem;
}

.sm-crypto-proc {
  min-width: 0;
}

.sm-crypto-proc-title {
  display: block;
  margin-bottom: 0.22rem;
  padding-bottom: 0.12rem;
  border-bottom: 1px solid #6b7280;
  color: #3f7a5a;
  font-weight: 700;
  line-height: 1.2;
}

.sm-crypto-proc-corr .sm-crypto-proc-title {
  color: #dc2626;
}

.sm-crypto-proc-chall .sm-crypto-proc-title {
  color: #2563eb;
}

.sm-crypto-proc-leak .sm-crypto-proc-title {
  color: #7c3aed;
}

.sm-crypto-proc-win .sm-crypto-proc-title,
.sm-crypto-proc-gate .sm-crypto-proc-title,
.sm-crypto-proc-init .sm-crypto-proc-title {
  color: #111827;
}

.sm-crypto-game-line {
  margin: 0.12rem 0;
  overflow-wrap: anywhere;
  font-size: 0.82rem;
}

.sm-crypto-game-side {
  display: flex;
  flex-direction: column;
  gap: 1.2rem;
  align-items: stretch;
  padding-top: 1.8rem;
}

.sm-crypto-legend {
  display: flex;
  flex-direction: column;
  gap: 0.55rem;
  align-items: center;
  font-size: 1rem;
  font-weight: 700;
}

.sm-crypto-legend-comm {
  color: #3f7a5a;
}

.sm-crypto-legend-corr {
  color: #dc2626;
}

.sm-crypto-legend-chall {
  color: #2563eb;
}

.sm-crypto-legend-leak {
  color: #7c3aed;
}

.sm-crypto-security-box {
  padding: 0.65rem 0.75rem;
  border: 1px solid #93c5fd;
  border-radius: 5px;
  background: #eff6ff;
}

.sm-crypto-security-title {
  display: block;
  margin-bottom: 0.35rem;
  color: #111827;
  font-size: 1rem;
  font-weight: 700;
}

.sm-crypto-security-box-small {
  background: #f8fafc;
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

.sm-cka-diagram {
  margin: 1.2rem 0 1.5rem;
  max-width: 100%;
}

.sm-cka-caption {
  margin: 0 0 0.65rem;
  color: #1e293b;
  font-weight: 700;
  line-height: 1.35;
}

.sm-cka-round-equation {
  display: flex;
  flex-wrap: wrap;
  gap: 0.35rem 0.6rem;
  align-items: center;
  margin: 0 0 0.8rem;
  padding: 0.55rem 0.7rem;
  border: 1px solid #d8dee8;
  border-left: 3px solid #334155;
  border-radius: 5px;
  background: #f8fafc;
}

.sm-cka-equation-sep {
  color: #64748b;
  font-size: 0.82rem;
  font-weight: 700;
  line-height: 1.25;
  text-transform: uppercase;
}

.sm-cka-two-party {
  display: grid;
  grid-template-columns: minmax(18rem, 1fr) minmax(8rem, 0.32fr) minmax(18rem, 1fr);
  gap: 0.9rem;
  align-items: center;
}

.sm-cka-sequence {
  display: grid;
  grid-template-columns: minmax(16rem, 1fr) minmax(9rem, 0.42fr) minmax(16rem, 1fr);
  gap: 0.55rem 0.75rem;
  align-items: stretch;
}

.sm-cka-seq-party {
  display: block;
  padding: 0.35rem 0 0.45rem;
  border-bottom: 2px solid #cbd5e1;
  color: #334155;
  font-size: 0.8rem;
  font-weight: 700;
  line-height: 1.25;
  text-transform: uppercase;
}

.sm-cka-seq-party.sm-cka-party-a {
  border-top: 0;
  border-bottom-color: #2563eb;
}

.sm-cka-seq-party.sm-cka-party-b {
  border-top: 0;
  border-bottom-color: #0f766e;
}

.sm-cka-seq-channel {
  text-align: center;
}

.sm-cka-seq-cell,
.sm-cka-seq-check,
.sm-cka-seq-note {
  min-width: 0;
  padding: 0.55rem 0.65rem;
  border: 1px solid #d8dee8;
  border-left-width: 3px;
  border-radius: 5px;
  background: #ffffff;
}

.sm-cka-seq-state {
  border-left-color: #2563eb;
  background: #f8fbff;
}

.sm-cka-seq-op {
  border-left-color: #0f766e;
  background: #f7fffb;
}

.sm-cka-seq-check {
  display: flex;
  align-items: center;
  justify-content: center;
  border-left-color: #7c3aed;
  background: #faf5ff;
  color: #581c87;
  font-weight: 700;
  text-align: center;
}

.sm-cka-seq-note {
  border-left-color: #64748b;
  background: #f8fafc;
  color: #475569;
  font-size: 0.86rem;
  line-height: 1.4;
}

.sm-cka-seq-gap {
  min-height: 1px;
}

.sm-cka-seq-title {
  display: block;
  margin-bottom: 0.18rem;
  color: #475569;
  font-size: 0.72rem;
  font-weight: 700;
  line-height: 1.2;
  text-transform: uppercase;
}

.sm-cka-seq-body {
  display: block;
  overflow-wrap: anywhere;
}

.sm-cka-seq-message {
  display: flex;
  min-width: 0;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 0.22rem;
  color: #7f1d1d;
  font-size: 0.82rem;
  font-weight: 700;
  line-height: 1.25;
  text-align: center;
}

.sm-cka-party,
.sm-cka-game-node,
.sm-cka-state-summary {
  min-width: 0;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #ffffff;
}

.sm-cka-party {
  padding: 0.85rem;
}

.sm-cka-party-a {
  border-top: 3px solid #2563eb;
}

.sm-cka-party-b {
  border-top: 3px solid #0f766e;
}

.sm-cka-party-title,
.sm-cka-step-title,
.sm-cka-game-title,
.sm-cka-state-title {
  display: block;
  color: #334155;
  font-size: 0.76rem;
  font-weight: 700;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.sm-cka-step {
  display: grid;
  grid-template-columns: minmax(6.8rem, 0.42fr) minmax(0, 1fr);
  gap: 0.45rem;
  align-items: baseline;
  margin-top: 0.5rem;
  padding: 0.48rem 0.55rem;
  border: 1px solid #dfe7f1;
  border-radius: 5px;
  background: #f8fafc;
}

.sm-cka-step-state {
  background: #eff6ff;
}

.sm-cka-step-op {
  background: #f0fdfa;
}

.sm-cka-step-check {
  background: #faf5ff;
}

.sm-cka-step-body,
.sm-cka-game-body,
.sm-cka-state-body {
  display: block;
  overflow-wrap: anywhere;
}

.sm-cka-wire,
.sm-cka-lens-arrow,
.sm-cka-game-arrow {
  display: flex;
  min-width: 0;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 0.25rem;
  color: #7f1d1d;
  font-size: 0.82rem;
  font-weight: 700;
  line-height: 1.25;
  text-align: center;
}

.sm-cka-wire-line {
  position: relative;
  display: block;
  width: 100%;
  min-width: 6.5rem;
  height: 1.3rem;
}

.sm-cka-wire-line::before {
  content: "";
  position: absolute;
  top: 0.62rem;
  left: 0;
  right: 0.25rem;
  border-top: 2px solid #b91c1c;
}

.sm-cka-wire-line::after {
  content: "";
  position: absolute;
  top: 0.35rem;
  right: 0;
  width: 0.55rem;
  height: 0.55rem;
  border-top: 2px solid #b91c1c;
  border-right: 2px solid #b91c1c;
  transform: rotate(45deg);
}

.sm-cka-wire-label {
  padding: 0.16rem 0.35rem;
  border: 1px solid #d8dee8;
  border-radius: 999px;
  background: #ffffff;
}

.sm-cka-lens {
  display: grid;
  grid-template-columns: minmax(0, 1fr) minmax(13rem, 0.55fr) minmax(0, 1fr);
  gap: 0.85rem;
  align-items: center;
  margin-top: 0.9rem;
}

.sm-cka-state-summary {
  padding: 0.7rem 0.8rem;
  background: #f8fafc;
  line-height: 1.45;
}

.sm-cka-game-stack {
  display: grid;
  grid-template-columns: minmax(0, 1fr);
  gap: 0.55rem;
}

.sm-cka-game-node {
  padding: 0.7rem 0.8rem;
}

.sm-cka-game-paper {
  border-left: 3px solid #0f766e;
}

.sm-cka-game-spec {
  border-left: 3px solid #2563eb;
}

.sm-cka-game-impl {
  border-left: 3px solid #c2410c;
}

.sm-cka-game-exp {
  border-left: 3px solid #7c3aed;
}

.sm-cka-game-reduction {
  border-left: 3px solid #b91c1c;
}

@media (max-width: 900px) {
  .sm-game-grid {
    grid-template-columns: minmax(0, 1fr);
  }

  .sm-fm-roll-grid,
  .sm-fm-bind-grid,
  .sm-fm-flow,
  .sm-cka-two-party,
  .sm-cka-sequence,
  .sm-crypto-flow-grid,
  .sm-crypto-game-layout,
  .sm-cka-lens {
    grid-template-columns: minmax(0, 1fr);
  }

  .sm-crypto-proc-grid {
    grid-template-columns: minmax(0, 1fr);
  }

  .sm-fm-bind-arrow,
  .sm-fm-flow-arrow,
  .sm-cka-wire,
  .sm-cka-lens-arrow {
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
  margin: 1.05rem 0 1.3rem;
  padding-top: 0.25rem;
  border-top: 1px solid #eef2f7;
}

.sm-triptych-title {
  margin: 0 0 0.5rem;
  font-size: 1.05rem;
  line-height: 1.35;
  letter-spacing: 0;
}

.sm-triptych-grid {
  display: grid;
  grid-template-columns: minmax(0, 1fr);
  gap: 0.5rem;
  align-items: start;
}

.sm-triptych-panel {
  min-width: 0;
  padding: 0;
  border: 0;
  background: transparent;
}

.sm-triptych-paper {
  padding-left: 0;
}

.sm-triptych-lean {
  padding-left: 0;
}

.sm-triptych-meaning {
  padding-left: 0;
}

.sm-triptych-panel-title {
  margin: 0 0 0.18rem;
  color: #475569;
  font-size: 0.72rem;
  font-weight: 700;
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

private partial def outputDir? : List String → Option System.FilePath
  | "--output" :: path :: _ => some path
  | _ :: rest => outputDir? rest
  | [] => none

private partial def copyHoverDocsToSubdirs (root : System.FilePath) : IO Unit := do
  let docsPath := root / "-verso-docs.json"
  unless ← docsPath.pathExists do
    return ()
  let docs ← IO.FS.readFile docsPath
  let rec visit (dir : System.FilePath) : IO Unit := do
    for entry in ← dir.readDir do
      if ← entry.path.isDir then
        IO.FS.writeFile (entry.path / "-verso-docs.json") docs
        visit entry.path
  visit root

def main (args : List String) : IO UInt32 := do
  let exitCode ← PreviewManifest.manualMainWithSharedPreviewManifest
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
  if exitCode == 0 then
    if let some out := outputDir? args then
      copyHoverDocsToSubdirs (out / "html-multi")
  pure exitCode
