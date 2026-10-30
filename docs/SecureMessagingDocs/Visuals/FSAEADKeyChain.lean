/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

open Verso Genre Manual Doc Elab
open Lean

/-- The PRG chain of the FS-AEAD from AEAD and PRG, with `w_0 = k` and
`(w_j, K_j) ← G(w_{j-1})`. A encrypts its `j`-th message under `K_j`. The example shows B after
message 3 arrives first: `skip(3)` stores `K_1` and `K_2` in `D`, then `K_3` decrypts the message
and B's seed is `w_3`. -/
private def fsAeadKeyChainSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="kc-text" viewBox="0 32 880 280" width="880" height="280" style="display:block;width:100%;height:auto" role="img" aria-label="The key chain. Each G box has two outputs: the next seed to the right and a key below. Starting from the shared key w0 = k, each application of the PRG G turns seed w(j-1) into the next seed w(j) and the AEAD key K(j). A encrypts its j-th message under K(j). Example: B receives message 3 first. B skips indices 1 and 2 and stores K1 and K2 in the dictionary D, uses K3 to decrypt message 3, and keeps the seed w3 with iB = 3. The seeds w0 to w2 are overwritten, and w4 and K4 are not derived yet.">
  <!--
    Units are viewBox pixels (the viewBox starts at y = 32). Seed w_j is at x = 140 + 150 j (64 wide), the G box after it at
    x = 224 + 150 j (40 wide), and the key K_(j+1) under that G box. Rows: seeds at y = 70,
    keys at y = 150. Classes: kc-secret current secret (amber); kc-stored key kept in D
    (hatched); kc-gone overwritten or not yet derived (dashed, muted).
  -->
  <defs>
    <marker id="kc-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <pattern id="kc-hatch" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <rect width="7" height="7" fill="#fff6e0"/>
      <line x1="0" y1="0" x2="0" y2="7" stroke="#d29a2a" stroke-width="2.2"/>
    </pattern>
    <style>
      .kc-text   { font-family: Arial, Helvetica, sans-serif; font-size: 17px; fill: #171717; }
      .kc-small  { font-size: 14px; }
      .kc-math   { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 20px; }
      .kc-sub    { baseline-shift: -5px; font-size: 13px; }
      .kc-muted  { fill: #5f5f5f; }
      .kc-box    { fill: white; stroke: #252525; stroke-width: 1.2; }
      .kc-secret { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .kc-stored { stroke: #b7791f; stroke-width: 1.4; }
      .kc-gone   { fill: white; stroke: #8a8a8a; stroke-width: 1; stroke-dasharray: 4 3; }
      .kc-flow   { fill: none; stroke: #252525; stroke-width: 1.3; }
      .kc-halo   { paint-order: stroke; stroke: white; stroke-width: 4px; stroke-linejoin: round; }
    </style>
  </defs>

  <!-- Row labels. -->
  <text class="kc-small" x="12" y="95">seeds</text>
  <text class="kc-small" x="12" y="175">AEAD keys</text>

  <!-- Seeds w0 = k, w1 and w2: overwritten. -->
  <rect class="kc-gone" x="140" y="70" width="64" height="40"/>
  <text class="kc-math kc-muted" x="172" y="96" text-anchor="middle">w<tspan class="kc-sub">0</tspan></text>
  <text class="kc-small kc-muted" x="172" y="128" text-anchor="middle">= <tspan class="kc-math" style="font-size:17px">k</tspan></text>
  <rect class="kc-gone" x="290" y="70" width="64" height="40"/>
  <text class="kc-math kc-muted" x="322" y="96" text-anchor="middle">w<tspan class="kc-sub">1</tspan></text>
  <rect class="kc-gone" x="440" y="70" width="64" height="40"/>
  <text class="kc-math kc-muted" x="472" y="96" text-anchor="middle">w<tspan class="kc-sub">2</tspan></text>
  <!-- Seed w3: B's current seed. -->
  <rect class="kc-secret" x="590" y="70" width="64" height="40"/>
  <text class="kc-math" x="622" y="96" text-anchor="middle">w<tspan class="kc-sub">3</tspan></text>
  <text class="kc-small" x="622" y="46" text-anchor="middle">B's seed, <tspan class="kc-math" style="font-size:17px">i</tspan><tspan class="kc-sub">B</tspan> = 3</text>
  <path class="kc-flow" marker-end="url(#kc-arrow)" d="M622 52 V68"/>
  <!-- Seed w4: not derived yet. -->
  <rect class="kc-gone" x="740" y="70" width="64" height="40"/>
  <text class="kc-math kc-muted" x="772" y="96" text-anchor="middle">w<tspan class="kc-sub">4</tspan></text>
  <path class="kc-flow" marker-end="url(#kc-arrow)" d="M804 90 H822"/>
  <text x="838" y="96">…</text>

  <!-- G boxes: seed in, next seed right, key down. -->
  <g class="kc-small" text-anchor="middle">
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M204 90 H222"/>
    <rect class="kc-box" x="224" y="70" width="40" height="40"/>
    <text class="kc-math" x="244" y="96">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M264 90 H288"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M244 110 V148"/>
    <!-- Labels of the two outputs of G, on the first G box only. -->
    <text class="kc-muted" x="276" y="62">next seed</text>
    <text class="kc-muted" x="250" y="134" text-anchor="start">key</text>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M354 90 H372"/>
    <rect class="kc-box" x="374" y="70" width="40" height="40"/>
    <text class="kc-math" x="394" y="96">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M414 90 H438"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M394 110 V148"/>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M504 90 H522"/>
    <rect class="kc-box" x="524" y="70" width="40" height="40"/>
    <text class="kc-math" x="544" y="96">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M564 90 H588"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M544 110 V148"/>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M654 90 H672"/>
    <rect class="kc-gone" x="674" y="70" width="40" height="40"/>
    <text class="kc-math kc-muted" x="694" y="96">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M714 90 H738"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M694 110 V148"/>
  </g>

  <!-- Keys K1 and K2: messages not received yet, stored in D. -->
  <rect class="kc-stored" fill="url(#kc-hatch)" x="212" y="150" width="64" height="40"/>
  <text class="kc-math kc-halo" x="244" y="176" text-anchor="middle">K<tspan class="kc-sub">1</tspan></text>
  <rect class="kc-stored" fill="url(#kc-hatch)" x="362" y="150" width="64" height="40"/>
  <text class="kc-math kc-halo" x="394" y="176" text-anchor="middle">K<tspan class="kc-sub">2</tspan></text>
  <path class="kc-flow" d="M216 200 V206 H422 V200"/>
  <text class="kc-small" x="319" y="226" text-anchor="middle">messages 1 and 2 not received yet,</text>
  <text class="kc-small" x="319" y="244" text-anchor="middle">keys kept in <tspan class="kc-math" style="font-size:17px">D</tspan>[1], <tspan class="kc-math" style="font-size:17px">D</tspan>[2]</text>
  <!-- Key K3: message 3, received first. -->
  <rect class="kc-box" x="512" y="150" width="64" height="40"/>
  <text class="kc-math" x="544" y="176" text-anchor="middle">K<tspan class="kc-sub">3</tspan></text>
  <text class="kc-small" x="544" y="226" text-anchor="middle">message 3, received first</text>
  <!-- Key K4: not derived yet. -->
  <rect class="kc-gone" x="662" y="150" width="64" height="40"/>
  <text class="kc-math kc-muted" x="694" y="176" text-anchor="middle">K<tspan class="kc-sub">4</tspan></text>
  <text class="kc-small kc-muted" x="694" y="226" text-anchor="middle">not derived yet</text>

  <!-- Legend. -->
  <g class="kc-small">
    <rect class="kc-secret" x="12" y="274" width="26" height="18"/>
    <text x="46" y="288">B's current seed</text>
    <rect class="kc-stored" x="200" y="274" width="26" height="18" fill="url(#kc-hatch)"/>
    <text x="234" y="288">key of a skipped index, kept in <tspan class="kc-math" style="font-size:16px">D</tspan></text>
    <rect class="kc-gone" x="520" y="274" width="26" height="18"/>
    <text x="554" y="288">overwritten, or not derived yet</text>
  </g>
</svg>
"##

/-- Embed the illustration of the FS-AEAD key chain using Verso's SVG renderer. -/
@[directive]
def fsAeadKeyChainIllustration : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote fsAeadKeyChainSvg) "100%" "\\textwidth" false) #[])
