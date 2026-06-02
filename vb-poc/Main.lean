/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import SMDocs.Contents

/-!
# Site generator

Renders the Verso-Blueprint site to static HTML. From the repository root:

    lake -d vb-poc build SMDocs
    lake -d vb-poc env lean --run vb-poc/Main.lean --output vb-poc/_out/site

The site lands in `vb-poc/_out/site/html-multi/`.
-/

open Verso Doc
open Verso.Genre Manual

/-- Stylesheet for the custom diagram blocks. Verso does **not** auto-collect CSS:
classes emitted by a `block_extension` only take effect when the matching rules are
attached here via `config.toHtmlAssets.extraCss`. This is the message-sequence-chart
("`:::msc`") family — a two-party flow grid, gray comments, coloured pill chips, and
ping-pong arrows whose line + arrowhead are pure CSS pseudo-elements. -/
def smCss : CSS := CSS.mk r#"
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
  color: #6b7280;
  font-size: 0.84rem;
  font-style: italic;
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
  background: transparent;
}

.sm-crypto-chip-comm {
  background: #3f7a5a;
}

.sm-crypto-chip-key {
  background: #2563eb;
}

.sm-crypto-chip-ok {
  background: #bb2528;
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

@media (max-width: 900px) {
  .sm-crypto-flow-grid {
    grid-template-columns: minmax(0, 1fr);
  }
}

.bp_math.display {
  overflow-x: auto;
  max-width: 100%;
}
"#

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc SMDocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := { toHtmlAssets := { features := .all, extraCss := .ofList [smCss] } })
