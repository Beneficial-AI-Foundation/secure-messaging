/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

open Verso Genre Manual Doc Elab
open Lean

/-- Key material of a party `X` across consecutive states and the coins sampled by its sends.
Material of epoch `t` enters with the coins of a send, stays in the state until a receive erases
it, and the coins of a later send yield the epoch key. Below each state is `vuln^corr_X` of that
state, exposed by `O-Corr-X`; above each send is `vuln^rleak_X` of the state before the send and
its coins, exposed by `O-Send-X-rleak`. -/
private def sckaKeyMaterialIllustrationSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="km-text" viewBox="0 146 1110 264" width="1110" height="264" style="display:block;width:100%;height:auto" role="img" aria-label="Key material accumulates in the states and send coins of a party X. Five consecutive states st(0) to st(4) are linked by Send, Rec, Send and Rec. The first send samples coins r(1) that carry key material of epoch t, which then stays in the state; the second send samples coins r(3) and outputs the epoch key I_t; the last receive erases the material and moves to epoch t+1. Below each state are its vulnerable epochs, exposed by O-Corr-X; they contain t exactly while the state holds material of epoch t. Above each send are the vulnerable epochs of its coins, exposed by O-Send-X-rleak; they contain t.">
  <!--
    Key material and vulnerable epochs of a generic party X.
    Units are viewBox pixels (the viewBox starts at y = 146). Each state, operation and epoch strip
    is a group placed by its transform. States are 112 wide and operations 64 wide, with 18-pixel
    arrows between them (a period of 212). Classes: km-secret secret key material (amber);
    km-vuln vulnerable epochs (hatched); km-math italic math; km-sub and km-sup scripts.
  -->
  <defs>
    <marker id="km-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <pattern id="km-hatch" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <rect width="7" height="7" fill="#fff6e0"/>
      <line x1="0" y1="0" x2="0" y2="7" stroke="#d29a2a" stroke-width="2.2"/>
    </pattern>
    <style>
      .km-text   { font-family: Arial, Helvetica, sans-serif; font-size: 17px; fill: #171717; }
      .km-small  { font-size: 14px; }
      .km-math   { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 20px; }
      .km-sub    { baseline-shift: -5px; font-size: 13px; }
      .km-sup    { baseline-shift: 7px; font-size: 12px; }
      .km-red    { fill: #b42318; }
      .km-muted  { fill: #5f5f5f; }
      .km-box    { fill: white; stroke: #252525; stroke-width: 1.2; }
      .km-secret { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .km-flow   { fill: none; stroke: #252525; stroke-width: 1.3; }
      .km-cell   { fill: white; stroke: #8a8a8a; stroke-width: 1; }
      .km-vuln   { stroke: #b7791f; stroke-width: 1.4; }
      .km-halo   { paint-order: stroke; stroke: white; stroke-width: 4px; stroke-linejoin: round; }
      .km-cellt  { font-size: 13px; }
      .km-cellt .km-math { font-size: 16px; }
    </style>
  </defs>

  <!-- Row labels: the oracle that exposes the epochs of each row. -->
  <text class="km-red km-small" x="12" y="175">O-Send-X-rleak</text>
  <text class="km-small" x="12" y="237">party X</text>
  <text class="km-red km-small" x="12" y="305">O-Corr-X</text>

  <!-- st(0): no key material. -->
  <g transform="translate(135,196)">
    <rect class="km-box" width="112" height="72"/>
    <text x="10" y="22">st<tspan class="km-sup">(0)</tspan></text>
  </g>
  <!-- Vulnerable epochs of st(0), exposed by O-Corr-X. -->
  <g text-anchor="middle" transform="translate(146,286)">
    <rect class="km-cell" width="30" height="28"/>
    <rect class="km-cell" x="30" width="30" height="28"/>
    <rect class="km-cell" x="60" width="30" height="28"/>
    <text class="km-cellt" x="15" y="19"><tspan class="km-math">t</tspan>−1</text>
    <text class="km-cellt" x="45" y="19"><tspan class="km-math">t</tspan></text>
    <text class="km-cellt" x="75" y="19"><tspan class="km-math">t</tspan>+1</text>
  </g>
  <!-- st(1): holds key material of epoch t. -->
  <g transform="translate(347,196)">
    <rect class="km-box" width="112" height="72"/>
    <text x="10" y="22">st<tspan class="km-sup">(1)</tspan></text>
    <rect class="km-secret" x="14" y="30" width="84" height="24"/>
    <text class="km-math" x="56" y="48" text-anchor="middle" style="font-size:18px">t</text>
  </g>
  <!-- Vulnerable epochs of st(1), exposed by O-Corr-X. -->
  <g text-anchor="middle" transform="translate(358,286)">
    <rect class="km-cell" width="30" height="28"/>
    <rect class="km-vuln" fill="url(#km-hatch)" x="30" width="30" height="28"/>
    <rect class="km-cell" x="60" width="30" height="28"/>
    <text class="km-cellt" x="15" y="19"><tspan class="km-math">t</tspan>−1</text>
    <text class="km-cellt km-halo" x="45" y="19"><tspan class="km-math">t</tspan></text>
    <text class="km-cellt" x="75" y="19"><tspan class="km-math">t</tspan>+1</text>
  </g>
  <!-- st(2): holds key material of epoch t. -->
  <g transform="translate(559,196)">
    <rect class="km-box" width="112" height="72"/>
    <text x="10" y="22">st<tspan class="km-sup">(2)</tspan></text>
    <rect class="km-secret" x="14" y="30" width="84" height="24"/>
    <text class="km-math" x="56" y="48" text-anchor="middle" style="font-size:18px">t</text>
  </g>
  <!-- Vulnerable epochs of st(2), exposed by O-Corr-X. -->
  <g text-anchor="middle" transform="translate(570,286)">
    <rect class="km-cell" width="30" height="28"/>
    <rect class="km-vuln" fill="url(#km-hatch)" x="30" width="30" height="28"/>
    <rect class="km-cell" x="60" width="30" height="28"/>
    <text class="km-cellt" x="15" y="19"><tspan class="km-math">t</tspan>−1</text>
    <text class="km-cellt km-halo" x="45" y="19"><tspan class="km-math">t</tspan></text>
    <text class="km-cellt" x="75" y="19"><tspan class="km-math">t</tspan>+1</text>
  </g>
  <!-- st(3): holds key material of epoch t. -->
  <g transform="translate(771,196)">
    <rect class="km-box" width="112" height="72"/>
    <text x="10" y="22">st<tspan class="km-sup">(3)</tspan></text>
    <rect class="km-secret" x="14" y="30" width="84" height="24"/>
    <text class="km-math" x="56" y="48" text-anchor="middle" style="font-size:18px">t</text>
  </g>
  <!-- Vulnerable epochs of st(3), exposed by O-Corr-X. -->
  <g text-anchor="middle" transform="translate(782,286)">
    <rect class="km-cell" width="30" height="28"/>
    <rect class="km-vuln" fill="url(#km-hatch)" x="30" width="30" height="28"/>
    <rect class="km-cell" x="60" width="30" height="28"/>
    <text class="km-cellt" x="15" y="19"><tspan class="km-math">t</tspan>−1</text>
    <text class="km-cellt km-halo" x="45" y="19"><tspan class="km-math">t</tspan></text>
    <text class="km-cellt" x="75" y="19"><tspan class="km-math">t</tspan>+1</text>
  </g>
  <!-- st(4): material of t erased; epoch t+1. -->
  <g transform="translate(983,196)">
    <rect class="km-box" width="112" height="72"/>
    <text x="10" y="22">st<tspan class="km-sup">(4)</tspan></text>
  </g>
  <!-- Vulnerable epochs of st(4), exposed by O-Corr-X. -->
  <g text-anchor="middle" transform="translate(994,286)">
    <rect class="km-cell" width="30" height="28"/>
    <rect class="km-cell" x="30" width="30" height="28"/>
    <rect class="km-cell" x="60" width="30" height="28"/>
    <text class="km-cellt" x="15" y="19"><tspan class="km-math">t</tspan>−1</text>
    <text class="km-cellt" x="45" y="19"><tspan class="km-math">t</tspan></text>
    <text class="km-cellt" x="75" y="19"><tspan class="km-math">t</tspan>+1</text>
  </g>
  <!-- Send: samples coins r(1) carrying key material of epoch t. -->
  <path class="km-flow" marker-end="url(#km-arrow)" d="M247 232 H263"/>
  <path class="km-flow" marker-end="url(#km-arrow)" d="M329 232 H345"/>
  <g class="km-small" text-anchor="middle" transform="translate(265,196)">
    <rect class="km-box" width="64" height="72"/>
    <text x="32" y="20">Send</text>
    <rect class="km-secret" x="8" y="30" width="48" height="26"/>
    <text class="km-math" x="32" y="50" style="font-size:19px">r<tspan class="km-sup">(1)</tspan></text>
  </g>
  <!-- Vulnerable epochs of the coins r(1), exposed by O-Send-X-rleak. -->
  <g text-anchor="middle" transform="translate(252,156)">
    <rect class="km-cell" width="30" height="28"/>
    <rect class="km-vuln" fill="url(#km-hatch)" x="30" width="30" height="28"/>
    <rect class="km-cell" x="60" width="30" height="28"/>
    <text class="km-cellt" x="15" y="19"><tspan class="km-math">t</tspan>−1</text>
    <text class="km-cellt km-halo" x="45" y="19"><tspan class="km-math">t</tspan></text>
    <text class="km-cellt" x="75" y="19"><tspan class="km-math">t</tspan>+1</text>
  </g>
  <!-- Rec: receives a message. -->
  <path class="km-flow" marker-end="url(#km-arrow)" d="M459 232 H475"/>
  <path class="km-flow" marker-end="url(#km-arrow)" d="M541 232 H557"/>
  <g class="km-small" text-anchor="middle" transform="translate(477,196)">
    <rect class="km-box" width="64" height="72"/>
    <text x="32" y="41">Rec</text>
  </g>
  <!-- Send: samples coins r(3) carrying key material of epoch t. -->
  <path class="km-flow" marker-end="url(#km-arrow)" d="M671 232 H687"/>
  <path class="km-flow" marker-end="url(#km-arrow)" d="M753 232 H769"/>
  <g class="km-small" text-anchor="middle" transform="translate(689,196)">
    <rect class="km-box" width="64" height="72"/>
    <text x="32" y="20">Send</text>
    <rect class="km-secret" x="8" y="30" width="48" height="26"/>
    <text class="km-math" x="32" y="50" style="font-size:19px">r<tspan class="km-sup">(3)</tspan></text>
  </g>
  <!-- Vulnerable epochs of the coins r(3), exposed by O-Send-X-rleak. -->
  <g text-anchor="middle" transform="translate(676,156)">
    <rect class="km-cell" width="30" height="28"/>
    <rect class="km-vuln" fill="url(#km-hatch)" x="30" width="30" height="28"/>
    <rect class="km-cell" x="60" width="30" height="28"/>
    <text class="km-cellt" x="15" y="19"><tspan class="km-math">t</tspan>−1</text>
    <text class="km-cellt km-halo" x="45" y="19"><tspan class="km-math">t</tspan></text>
    <text class="km-cellt" x="75" y="19"><tspan class="km-math">t</tspan>+1</text>
  </g>
  <!-- Rec: erases the material of t and moves to t+1. -->
  <path class="km-flow" marker-end="url(#km-arrow)" d="M883 232 H899"/>
  <path class="km-flow" marker-end="url(#km-arrow)" d="M965 232 H981"/>
  <g class="km-small" text-anchor="middle" transform="translate(901,196)">
    <rect class="km-box" width="64" height="72"/>
    <text x="32" y="41">Rec</text>
  </g>
  <!-- The second send outputs the epoch key; the last receive erases its material. -->
  <path class="km-flow" marker-end="url(#km-arrow)" d="M721 268 V330"/>
  <text x="721" y="352" text-anchor="middle">(<tspan class="km-math">t</tspan>, <tspan class="km-math">I</tspan><tspan class="km-sub km-math">t</tspan>)</text>
  <text class="km-small km-muted" x="933" y="288" text-anchor="middle">erases <tspan class="km-math" style="font-size:16px">t</tspan></text>

  <!-- Legend. -->
  <g class="km-small">
    <rect class="km-secret" x="12" y="384" width="26" height="18"/>
    <text x="46" y="398">secret key material of epoch <tspan class="km-math" style="font-size:16px">t</tspan>, in a state or in the coins of a send</text>
    <rect class="km-vuln" x="560" y="384" width="26" height="18" fill="url(#km-hatch)"/>
    <text x="594" y="398">vulnerable epochs: keys computable by leaking party state or random coins</text>
  </g>
</svg>
"##

/-- Embed the illustration of the SCKA key material using Verso's SVG renderer. -/
@[directive]
def sckaKeyMaterialIllustration : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote sckaKeyMaterialIllustrationSvg) "100%" "\\textwidth" false) #[])
