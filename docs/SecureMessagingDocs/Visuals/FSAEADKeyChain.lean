/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

open Verso Genre Manual Doc Elab
open Lean

/-- The PRG chains of A and B in the FS-AEAD from AEAD and PRG, with `w_0 = k` and
`(w_j, K_j) ← G(w_{j-1})`. A has sent three messages, each encrypted under its own `K_j`.
Message 3 reaches B first, so B runs `skip(3)`, keeps `K_1` and `K_2` in `D`, decrypts with
`K_3`, and its seed is `w_3`. -/
private def fsAeadKeyChainSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="kc-text" viewBox="0 0 880 500" width="880" height="500" style="display:block;width:100%;height:auto" role="img" aria-label="The key chains of A and B. Both start from the shared key w0 = k. Each application of the PRG G turns seed w(j-1) into the next seed w(j) and the AEAD key K(j). A has sent three messages: it encrypted message j under K(j), sent (j, e(j)), deleted K(j), and keeps the seed w3 with iA = 3. Message 3 reaches B first; messages 1 and 2 are still in transit. B skips indices 1 and 2 and stores K1 and K2 in the dictionary D, decrypts message 3 with K3, and keeps the seed w3 with iB = 3. The seeds w0 to w2 are deleted (grey), and w4 and K4 are not derived yet on either side (dotted).">
  <!--
    Units are viewBox pixels. In both lanes, seed w_j is at x = 140 + 150 j (64 wide), the G
    box after it at x = 224 + 150 j (40 wide), and the key K_(j+1) at x = 212 + 150 j, under
    or over that G box. A's lane: seeds at y = 40, keys at y = 120. B's lane is mirrored:
    keys at y = 290, seeds at y = 370, so that both key rows face the network band between
    them. Classes: kc-secret current seed (amber); kc-stored key kept in D (hatched); kc-gone
    deleted (grey, dashed); kc-future not derived yet (dotted, faint); kc-transit message
    not delivered yet.
  -->
  <defs>
    <marker id="kc-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <pattern id="kc-hatch" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <rect width="7" height="7" fill="#fff6e0"/>
      <line x1="0" y1="0" x2="0" y2="7" stroke="#d29a2a" stroke-width="2.2"/>
    </pattern>
    <style>
      .kc-text    { font-family: Arial, Helvetica, sans-serif; font-size: 17px; fill: #171717; }
      .kc-small   { font-size: 14px; }
      .kc-party   { font-size: 18px; font-weight: bold; }
      .kc-math    { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 20px; }
      .kc-msg     { font-family: "Times New Roman", Times, serif; font-size: 17px; }
      .kc-sub     { baseline-shift: -5px; font-size: 13px; }
      .kc-muted   { fill: #5f5f5f; }
      .kc-box     { fill: white; stroke: #252525; stroke-width: 1.2; }
      .kc-secret  { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .kc-stored  { stroke: #b7791f; stroke-width: 1.4; }
      .kc-gone    { fill: #e8e8e8; stroke: #8a8a8a; stroke-width: 1; stroke-dasharray: 4 3; }
      .kc-future  { fill: white; stroke: #6f6f6f; stroke-width: 1.6; stroke-dasharray: 1.5 3.5; stroke-linecap: round; }
      .kc-faint   { fill: #8a8a8a; }
      .kc-flow    { fill: none; stroke: #252525; stroke-width: 1.3; }
      .kc-transit { stroke-dasharray: 5 4; }
      .kc-halo    { paint-order: stroke; stroke: white; stroke-width: 4px; stroke-linejoin: round; }
    </style>
  </defs>

  <!-- Lane labels. -->
  <text class="kc-party" x="12" y="66">A</text>
  <text class="kc-small kc-muted" x="40" y="66">seeds</text>
  <text class="kc-small kc-muted" x="40" y="146">keys</text>
  <text class="kc-small kc-muted" x="12" y="222">network</text>
  <text class="kc-party" x="12" y="316">B</text>
  <text class="kc-small kc-muted" x="40" y="316">keys</text>
  <text class="kc-small kc-muted" x="40" y="396">seeds</text>

  <!-- ===== A's lane: seeds at y = 40, keys at y = 120. ===== -->
  <rect class="kc-gone" x="140" y="40" width="64" height="40"/>
  <text class="kc-math kc-muted" x="172" y="66" text-anchor="middle">w<tspan class="kc-sub">0</tspan></text>
  <text class="kc-small kc-muted" x="172" y="98" text-anchor="middle">= <tspan class="kc-math" style="font-size:17px">k</tspan></text>
  <rect class="kc-gone" x="290" y="40" width="64" height="40"/>
  <text class="kc-math kc-muted" x="322" y="66" text-anchor="middle">w<tspan class="kc-sub">1</tspan></text>
  <rect class="kc-gone" x="440" y="40" width="64" height="40"/>
  <text class="kc-math kc-muted" x="472" y="66" text-anchor="middle">w<tspan class="kc-sub">2</tspan></text>
  <rect class="kc-secret" x="590" y="40" width="64" height="40"/>
  <text class="kc-math" x="622" y="66" text-anchor="middle">w<tspan class="kc-sub">3</tspan></text>
  <text class="kc-small" x="622" y="18" text-anchor="middle">A's seed, <tspan class="kc-math" style="font-size:17px">i</tspan><tspan class="kc-sub">A</tspan> = 3</text>
  <path class="kc-flow" marker-end="url(#kc-arrow)" d="M622 24 V38"/>
  <rect class="kc-future" x="740" y="40" width="64" height="40"/>
  <text class="kc-math kc-faint" x="772" y="66" text-anchor="middle">w<tspan class="kc-sub">4</tspan></text>
  <path class="kc-flow" marker-end="url(#kc-arrow)" d="M804 60 H822"/>
  <text x="838" y="66">…</text>

  <g class="kc-small" text-anchor="middle">
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M204 60 H222"/>
    <rect class="kc-box" x="224" y="40" width="40" height="40"/>
    <text class="kc-math" x="244" y="66">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M264 60 H288"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M244 80 V118"/>
    <!-- Labels of the two outputs of G, on the first G box only. -->
    <text class="kc-muted" x="276" y="32">next seed</text>
    <text class="kc-muted" x="250" y="104" text-anchor="start">key</text>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M354 60 H372"/>
    <rect class="kc-box" x="374" y="40" width="40" height="40"/>
    <text class="kc-math" x="394" y="66">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M414 60 H438"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M394 80 V118"/>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M504 60 H522"/>
    <rect class="kc-box" x="524" y="40" width="40" height="40"/>
    <text class="kc-math" x="544" y="66">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M564 60 H588"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M544 80 V118"/>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M654 60 H672"/>
    <rect class="kc-future" x="674" y="40" width="40" height="40"/>
    <text class="kc-math kc-faint" x="694" y="66">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M714 60 H738"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M694 80 V118"/>
  </g>

  <!-- A's keys K1 to K3: each encrypted one message, then deleted. K4: not derived yet. -->
  <rect class="kc-gone" x="212" y="120" width="64" height="40"/>
  <text class="kc-math kc-muted" x="244" y="146" text-anchor="middle">K<tspan class="kc-sub">1</tspan></text>
  <rect class="kc-gone" x="362" y="120" width="64" height="40"/>
  <text class="kc-math kc-muted" x="394" y="146" text-anchor="middle">K<tspan class="kc-sub">2</tspan></text>
  <rect class="kc-gone" x="512" y="120" width="64" height="40"/>
  <text class="kc-math kc-muted" x="544" y="146" text-anchor="middle">K<tspan class="kc-sub">3</tspan></text>
  <rect class="kc-future" x="662" y="120" width="64" height="40"/>
  <text class="kc-math kc-faint" x="694" y="146" text-anchor="middle">K<tspan class="kc-sub">4</tspan></text>

  <!-- ===== Network: A sends (j, e_j) with e_j encrypted under K_j. ===== -->
  <!-- Messages 1 and 2: still in transit. -->
  <path class="kc-flow kc-transit" marker-end="url(#kc-arrow)" d="M244 162 V214"/>
  <text class="kc-msg" x="254" y="196">(1, <tspan font-style="italic">e</tspan><tspan class="kc-sub">1</tspan>)</text>
  <text class="kc-small kc-muted" x="254" y="214">in transit</text>
  <path class="kc-flow kc-transit" marker-end="url(#kc-arrow)" d="M394 162 V214"/>
  <text class="kc-msg" x="404" y="196">(2, <tspan font-style="italic">e</tspan><tspan class="kc-sub">2</tspan>)</text>
  <text class="kc-small kc-muted" x="404" y="214">in transit</text>
  <!-- Message 3: delivered first. -->
  <path class="kc-flow" marker-end="url(#kc-arrow)" d="M544 162 V288"/>
  <text class="kc-msg" x="554" y="222">(3, <tspan font-style="italic">e</tspan><tspan class="kc-sub">3</tspan>)</text>
  <text class="kc-small" x="554" y="240">arrives first</text>

  <!-- ===== B's lane, mirrored: keys at y = 290, seeds at y = 370. ===== -->
  <!-- Keys K1 and K2: messages not received yet, kept in D. K3: decrypts message 3. -->
  <rect class="kc-stored" fill="url(#kc-hatch)" x="212" y="290" width="64" height="40"/>
  <text class="kc-math kc-halo" x="244" y="316" text-anchor="middle">K<tspan class="kc-sub">1</tspan></text>
  <text class="kc-small" x="282" y="316"><tspan class="kc-math" style="font-size:17px">D</tspan>[1]</text>
  <rect class="kc-stored" fill="url(#kc-hatch)" x="362" y="290" width="64" height="40"/>
  <text class="kc-math kc-halo" x="394" y="316" text-anchor="middle">K<tspan class="kc-sub">2</tspan></text>
  <text class="kc-small" x="432" y="316"><tspan class="kc-math" style="font-size:17px">D</tspan>[2]</text>
  <rect class="kc-box" x="512" y="290" width="64" height="40"/>
  <text class="kc-math" x="544" y="316" text-anchor="middle">K<tspan class="kc-sub">3</tspan></text>
  <rect class="kc-future" x="662" y="290" width="64" height="40"/>
  <text class="kc-math kc-faint" x="694" y="316" text-anchor="middle">K<tspan class="kc-sub">4</tspan></text>

  <g class="kc-small" text-anchor="middle">
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M204 390 H222"/>
    <rect class="kc-box" x="224" y="370" width="40" height="40"/>
    <text class="kc-math" x="244" y="396">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M264 390 H288"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M244 370 V332"/>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M354 390 H372"/>
    <rect class="kc-box" x="374" y="370" width="40" height="40"/>
    <text class="kc-math" x="394" y="396">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M414 390 H438"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M394 370 V332"/>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M504 390 H522"/>
    <rect class="kc-box" x="524" y="370" width="40" height="40"/>
    <text class="kc-math" x="544" y="396">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M564 390 H588"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M544 370 V332"/>

    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M654 390 H672"/>
    <rect class="kc-future" x="674" y="370" width="40" height="40"/>
    <text class="kc-math kc-faint" x="694" y="396">G</text>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M714 390 H738"/>
    <path class="kc-flow" marker-end="url(#kc-arrow)" d="M694 370 V332"/>
  </g>

  <rect class="kc-gone" x="140" y="370" width="64" height="40"/>
  <text class="kc-math kc-muted" x="172" y="396" text-anchor="middle">w<tspan class="kc-sub">0</tspan></text>
  <text class="kc-small kc-muted" x="172" y="428" text-anchor="middle">= <tspan class="kc-math" style="font-size:17px">k</tspan></text>
  <rect class="kc-gone" x="290" y="370" width="64" height="40"/>
  <text class="kc-math kc-muted" x="322" y="396" text-anchor="middle">w<tspan class="kc-sub">1</tspan></text>
  <rect class="kc-gone" x="440" y="370" width="64" height="40"/>
  <text class="kc-math kc-muted" x="472" y="396" text-anchor="middle">w<tspan class="kc-sub">2</tspan></text>
  <rect class="kc-secret" x="590" y="370" width="64" height="40"/>
  <text class="kc-math" x="622" y="396" text-anchor="middle">w<tspan class="kc-sub">3</tspan></text>
  <path class="kc-flow" marker-end="url(#kc-arrow)" d="M622 428 V412"/>
  <text class="kc-small" x="622" y="446" text-anchor="middle">B's seed, <tspan class="kc-math" style="font-size:17px">i</tspan><tspan class="kc-sub">B</tspan> = 3</text>
  <rect class="kc-future" x="740" y="370" width="64" height="40"/>
  <text class="kc-math kc-faint" x="772" y="396" text-anchor="middle">w<tspan class="kc-sub">4</tspan></text>
  <path class="kc-flow" marker-end="url(#kc-arrow)" d="M804 390 H822"/>
  <text x="838" y="396">…</text>

  <!-- Legend. -->
  <g class="kc-small">
    <rect class="kc-secret" x="12" y="474" width="26" height="18"/>
    <text x="46" y="488">current seed</text>
    <rect class="kc-stored" x="160" y="474" width="26" height="18" fill="url(#kc-hatch)"/>
    <text x="194" y="488">key of a skipped index, kept in <tspan class="kc-math" style="font-size:16px">D</tspan></text>
    <rect class="kc-gone" x="470" y="474" width="26" height="18"/>
    <text x="504" y="488">deleted</text>
    <rect class="kc-future" x="590" y="474" width="26" height="18"/>
    <text x="624" y="488">not derived yet</text>
  </g>
</svg>
"##

/-- Embed the illustration of the FS-AEAD key chain using Verso's SVG renderer. -/
@[directive]
def fsAeadKeyChainIllustration : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote fsAeadKeyChainSvg) "100%" "\\textwidth" false) #[])
