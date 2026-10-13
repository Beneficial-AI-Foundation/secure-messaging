/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

open Verso Genre Manual Doc Elab
open Lean

/-- A's corruption vulnerability: `O-Corr-A` returns `st_A`, whose decapsulation key `dk_A`
gives the key of epoch `t_A` together with public values, so `vuln^corr_A(st_A) = {t_A}`. -/
private def oppUniKemVulnCorrASvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="ve-text" viewBox="0 0 520 506" width="520" height="506" style="display:block;width:100%;height:auto" role="img" aria-label="Corruption of A: O-Corr-A returns A's state st_A, which contains the decapsulation key dk_A. The key of A's current epoch t_A is computable from dk_A and public values, so vuln-corr_A(st_A) is the set containing t_A, and t_A is added to Exposed.">
  <!--
    Corruption of A: the figure for vuln^corr_A.
    Units are viewBox pixels. Each block is a group placed by its transform, so its contents use
    local coordinates. Classes: ve-math italic math; ve-sub and ve-sup sub- and superscripts;
    ve-secret secret key material (amber); ve-oracle and ve-leak oracles and values returned to the
    adversary (red); ve-vuln and ve-exposed vulnerable and exposed epochs.
    Layout: adversary top right; oracle with the state on the left; vulnerable epochs bottom right; legend at the bottom.
  -->
  <defs>
    <marker id="vca-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <marker id="vca-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#b42318" stroke-width="1.2"/></marker>
    <pattern id="vca-hatch" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <rect width="7" height="7" fill="#fff6e0"/>
      <line x1="0" y1="0" x2="0" y2="7" stroke="#d29a2a" stroke-width="2.2"/>
    </pattern>
    <style>
      .ve-text   { font-family: Arial, Helvetica, sans-serif; font-size: 18px; fill: #171717; }
      .ve-small  { font-size: 14px; }
      .ve-math   { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 21px; }
      .ve-sub    { baseline-shift: -5px; font-size: 14px; }
      .ve-sup    { baseline-shift: 8px; font-size: 12px; }
      .ve-sub .ve-math { font-size: inherit; }
      .ve-red    { fill: #b42318; }
      .ve-muted  { fill: #5f5f5f; }
      .ve-box    { fill: white; stroke: #252525; stroke-width: 1.2; }
      .ve-rule   { stroke: #252525; stroke-width: 1; }
      .ve-oracle { fill: none; stroke: #b42318; stroke-width: 1.4; }
      .ve-secret { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .ve-flow   { fill: none; stroke: #252525; stroke-width: 1.3; }
      .ve-leak   { fill: none; stroke: #b42318; stroke-width: 1.8; }
      .ve-cell   { fill: white; stroke: #8a8a8a; stroke-width: 1; }
      .ve-vuln   { stroke: #b7791f; stroke-width: 1.4; }
      .ve-exposed { fill: #b42318; stroke: #b42318; stroke-width: 1.4; }
      .ve-on-red { fill: white; }
      .ve-halo   { paint-order: stroke; stroke: white; stroke-width: 4px; stroke-linejoin: round; }
      .ve-cellt { font-size: 15px; }
      .ve-cellt .ve-math { font-size: 17px; }
      .ve-cellt .ve-sub { font-size: 11px; }
      .ve-legend { font-size: 14px; }
      .ve-legend .ve-math { font-size: 17px; }
      .ve-legend .ve-sub { font-size: 11px; }
    </style>
  </defs>

  <!-- Adversary: receives the revealed value. -->
  <g text-anchor="middle" transform="translate(320,12)">
    <rect class="ve-oracle" width="200" height="62"/>
    <text class="ve-red" x="100" y="24">Adversary 𝒜</text>
    <text x="100" y="52"><tspan class="ve-red">st<tspan class="ve-sub">A</tspan></tspan></text>
  </g>

  <!-- O-Corr-A returns the whole state st_A; the amber row is its secret key material. -->
  <g text-anchor="middle" transform="translate(8,96)">
    <rect class="ve-oracle" width="184" height="221"/>
    <text class="ve-red" x="92" y="22">O-Corr-A</text>
    <g transform="translate(12,34)">
      <rect class="ve-box" width="160" height="175"/>
      <text x="80" y="22">st<tspan class="ve-sub">A</tspan></text>
      <line class="ve-rule" x1="0" y1="32" x2="160" y2="32"/>
      <rect class="ve-secret" x="16" y="38" width="128" height="24"/>
      <text x="80" y="56">dk<tspan class="ve-sub">A</tspan></text>
      <text x="80" y="83">ek<tspan class="ve-sub">A</tspan></text>
      <text x="80" y="110">ct<tspan class="ve-sub">0</tspan></text>
      <text x="80" y="137"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
      <text x="80" y="164">…</text>
    </g>
  </g>

  <!-- The state goes to the adversary. -->
  <path class="ve-leak" marker-end="url(#vca-red-arrow)" d="M192 140 H420 V78"/>

  <!-- Vulnerable epochs (hatched) of the revealed value; the oracle adds them to Exposed (red). -->
  <g text-anchor="middle" transform="translate(360,346)">
    <rect class="ve-cell" x="0" y="0" width="40" height="30"/>
    <rect class="ve-vuln" x="40" y="0" width="40" height="30" fill="url(#vca-hatch)"/>
    <rect class="ve-cell" x="80" y="0" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>−1</text>
    <text class="ve-cellt ve-halo" x="60" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
    <text class="ve-cellt" x="100" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>+1</text>
    <path class="ve-flow" marker-end="url(#vca-arrow)" d="M60 32 V60"/>
    <rect class="ve-cell" x="0" y="64" width="40" height="30"/>
    <rect class="ve-exposed" x="40" y="64" width="40" height="30"/>
    <rect class="ve-cell" x="80" y="64" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>−1</text>
    <text class="ve-cellt ve-on-red" x="60" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
    <text class="ve-cellt" x="100" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>+1</text>
    <text x="-12" y="21" text-anchor="end">vuln<tspan class="ve-sub">A</tspan><tspan class="ve-sup" dx="-9">corr</tspan>(st<tspan class="ve-sub">A</tspan>) = {<tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>}</text>
    <text x="-12" y="85" text-anchor="end">Exposed</text>
  </g>

  <!-- Legend. -->
  <g class="ve-legend" transform="translate(14,459)">
    <rect class="ve-secret" width="22" height="16"/>
    <text x="28" y="13">secret key material of epoch <tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
    <rect class="ve-exposed" x="286" width="22" height="16"/>
    <text x="314" y="13">exposed</text>
    <rect class="ve-vuln" y="24" width="22" height="16" fill="url(#vca-hatch)"/>
    <text x="28" y="37" font-size="13">vulnerable epochs: keys computable by leaking party state or random coins</text>
  </g>
</svg>
"##

/-- Embed the illustration of corruption of A using Verso's SVG renderer. -/
@[directive]
def oppUniKemVulnCorrA : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote oppUniKemVulnCorrASvg) "100%" "\\textwidth" false) #[])

/-- B's corruption vulnerability: `O-Corr-B` returns `st_B`, whose offline encapsulation state
`st_ct` gives the key of epoch `t_B` together with public values, so
`vuln^corr_B(st_B) = {t_B}`. -/
private def oppUniKemVulnCorrBSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="ve-text" viewBox="0 0 520 506" width="520" height="506" style="display:block;width:100%;height:auto" role="img" aria-label="Corruption of B: O-Corr-B returns B's state st_B, which contains the offline encapsulation state st_ct. The key of B's current epoch t_B is computable from st_ct and public values, so vuln-corr_B(st_B) is the set containing t_B, and t_B is added to Exposed.">
  <!--
    Corruption of B: the figure for vuln^corr_B.
    Units are viewBox pixels. Each block is a group placed by its transform, so its contents use
    local coordinates. Classes: ve-math italic math; ve-sub and ve-sup sub- and superscripts;
    ve-secret secret key material (amber); ve-oracle and ve-leak oracles and values returned to the
    adversary (red); ve-vuln and ve-exposed vulnerable and exposed epochs.
    Layout: adversary top right; oracle with the state on the left; vulnerable epochs bottom right; legend at the bottom.
  -->
  <defs>
    <marker id="vcb-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <marker id="vcb-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#b42318" stroke-width="1.2"/></marker>
    <pattern id="vcb-hatch" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <rect width="7" height="7" fill="#fff6e0"/>
      <line x1="0" y1="0" x2="0" y2="7" stroke="#d29a2a" stroke-width="2.2"/>
    </pattern>
    <style>
      .ve-text   { font-family: Arial, Helvetica, sans-serif; font-size: 18px; fill: #171717; }
      .ve-small  { font-size: 14px; }
      .ve-math   { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 21px; }
      .ve-sub    { baseline-shift: -5px; font-size: 14px; }
      .ve-sup    { baseline-shift: 8px; font-size: 12px; }
      .ve-sub .ve-math { font-size: inherit; }
      .ve-red    { fill: #b42318; }
      .ve-muted  { fill: #5f5f5f; }
      .ve-box    { fill: white; stroke: #252525; stroke-width: 1.2; }
      .ve-rule   { stroke: #252525; stroke-width: 1; }
      .ve-oracle { fill: none; stroke: #b42318; stroke-width: 1.4; }
      .ve-secret { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .ve-flow   { fill: none; stroke: #252525; stroke-width: 1.3; }
      .ve-leak   { fill: none; stroke: #b42318; stroke-width: 1.8; }
      .ve-cell   { fill: white; stroke: #8a8a8a; stroke-width: 1; }
      .ve-vuln   { stroke: #b7791f; stroke-width: 1.4; }
      .ve-exposed { fill: #b42318; stroke: #b42318; stroke-width: 1.4; }
      .ve-on-red { fill: white; }
      .ve-halo   { paint-order: stroke; stroke: white; stroke-width: 4px; stroke-linejoin: round; }
      .ve-cellt { font-size: 15px; }
      .ve-cellt .ve-math { font-size: 17px; }
      .ve-cellt .ve-sub { font-size: 11px; }
      .ve-legend { font-size: 14px; }
      .ve-legend .ve-math { font-size: 17px; }
      .ve-legend .ve-sub { font-size: 11px; }
    </style>
  </defs>

  <!-- Adversary: receives the revealed value. -->
  <g text-anchor="middle" transform="translate(320,12)">
    <rect class="ve-oracle" width="200" height="62"/>
    <text class="ve-red" x="100" y="24">Adversary 𝒜</text>
    <text x="100" y="52"><tspan class="ve-red">st<tspan class="ve-sub">B</tspan></tspan></text>
  </g>

  <!-- O-Corr-B returns the whole state st_B; the amber row is its secret key material. -->
  <g text-anchor="middle" transform="translate(8,96)">
    <rect class="ve-oracle" width="184" height="248"/>
    <text class="ve-red" x="92" y="22">O-Corr-B</text>
    <g transform="translate(12,34)">
      <rect class="ve-box" width="160" height="202"/>
      <text x="80" y="22">st<tspan class="ve-sub">B</tspan></text>
      <line class="ve-rule" x1="0" y1="32" x2="160" y2="32"/>
      <text x="80" y="56">ek<tspan class="ve-sub">A</tspan></text>
      <text x="80" y="83">ct<tspan class="ve-sub">0</tspan></text>
      <text x="80" y="110">ct<tspan class="ve-sub">1</tspan></text>
      <rect class="ve-secret" x="16" y="119" width="128" height="24"/>
      <text x="80" y="137">st<tspan class="ve-sub">ct</tspan></text>
      <text x="80" y="164"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
      <text x="80" y="191">…</text>
    </g>
  </g>

  <!-- The state goes to the adversary. -->
  <path class="ve-leak" marker-end="url(#vcb-red-arrow)" d="M192 140 H420 V78"/>

  <!-- Vulnerable epochs (hatched) of the revealed value; the oracle adds them to Exposed (red). -->
  <g text-anchor="middle" transform="translate(360,346)">
    <rect class="ve-cell" x="0" y="0" width="40" height="30"/>
    <rect class="ve-vuln" x="40" y="0" width="40" height="30" fill="url(#vcb-hatch)"/>
    <rect class="ve-cell" x="80" y="0" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>−1</text>
    <text class="ve-cellt ve-halo" x="60" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
    <text class="ve-cellt" x="100" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>+1</text>
    <path class="ve-flow" marker-end="url(#vcb-arrow)" d="M60 32 V60"/>
    <rect class="ve-cell" x="0" y="64" width="40" height="30"/>
    <rect class="ve-exposed" x="40" y="64" width="40" height="30"/>
    <rect class="ve-cell" x="80" y="64" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>−1</text>
    <text class="ve-cellt ve-on-red" x="60" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
    <text class="ve-cellt" x="100" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>+1</text>
    <text x="-12" y="21" text-anchor="end">vuln<tspan class="ve-sub">B</tspan><tspan class="ve-sup" dx="-9">corr</tspan>(st<tspan class="ve-sub">B</tspan>) = {<tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>}</text>
    <text x="-12" y="85" text-anchor="end">Exposed</text>
  </g>

  <!-- Legend. -->
  <g class="ve-legend" transform="translate(14,459)">
    <rect class="ve-secret" width="22" height="16"/>
    <text x="28" y="13">secret key material of epoch <tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
    <rect class="ve-exposed" x="286" width="22" height="16"/>
    <text x="314" y="13">exposed</text>
    <rect class="ve-vuln" y="24" width="22" height="16" fill="url(#vcb-hatch)"/>
    <text x="28" y="37" font-size="13">vulnerable epochs: keys computable by leaking party state or random coins</text>
  </g>
</svg>
"##

/-- Embed the illustration of corruption of B using Verso's SVG renderer. -/
@[directive]
def oppUniKemVulnCorrB : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote oppUniKemVulnCorrBSvg) "100%" "\\textwidth" false) #[])

/-- A's leakage vulnerability: with `dk_A = ⊥`, `O-Send-A-rleak` runs `KeyGen` with coins `r_K`
and returns them; they determine `dk_A`, so `vuln^rleak_A(st_A, r_K) = {t_A}`. -/
private def oppUniKemVulnRleakASvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="ve-text" viewBox="0 0 520 506" width="520" height="506" style="display:block;width:100%;height:auto" role="img" aria-label="Randomness leakage by A: since dk_A is undefined, O-Send-A-rleak runs KeyGen with coins r_K and returns r_K to the adversary. The coins determine dk_A, so the key of A's current epoch t_A is computable from r_K and public values: vuln-rleak_A(st_A, r_K) is the set containing t_A, and t_A is added to Exposed.">
  <!--
    Randomness leakage by A: the figure for vuln^rleak_A.
    Units are viewBox pixels. Each block is a group placed by its transform, so its contents use
    local coordinates. Classes: ve-math italic math; ve-sub and ve-sup sub- and superscripts;
    ve-secret secret key material (amber); ve-oracle and ve-leak oracles and values returned to the
    adversary (red); ve-vuln and ve-exposed vulnerable and exposed epochs.
    Layout: adversary top right; state before the send on the left; leaking-send oracle on the right; vulnerable epochs bottom right.
  -->
  <defs>
    <marker id="vra-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <marker id="vra-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#b42318" stroke-width="1.2"/></marker>
    <pattern id="vra-hatch" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <rect width="7" height="7" fill="#fff6e0"/>
      <line x1="0" y1="0" x2="0" y2="7" stroke="#d29a2a" stroke-width="2.2"/>
    </pattern>
    <style>
      .ve-text   { font-family: Arial, Helvetica, sans-serif; font-size: 18px; fill: #171717; }
      .ve-small  { font-size: 14px; }
      .ve-math   { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 21px; }
      .ve-sub    { baseline-shift: -5px; font-size: 14px; }
      .ve-sup    { baseline-shift: 8px; font-size: 12px; }
      .ve-sub .ve-math { font-size: inherit; }
      .ve-red    { fill: #b42318; }
      .ve-muted  { fill: #5f5f5f; }
      .ve-box    { fill: white; stroke: #252525; stroke-width: 1.2; }
      .ve-rule   { stroke: #252525; stroke-width: 1; }
      .ve-oracle { fill: none; stroke: #b42318; stroke-width: 1.4; }
      .ve-secret { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .ve-flow   { fill: none; stroke: #252525; stroke-width: 1.3; }
      .ve-leak   { fill: none; stroke: #b42318; stroke-width: 1.8; }
      .ve-cell   { fill: white; stroke: #8a8a8a; stroke-width: 1; }
      .ve-vuln   { stroke: #b7791f; stroke-width: 1.4; }
      .ve-exposed { fill: #b42318; stroke: #b42318; stroke-width: 1.4; }
      .ve-on-red { fill: white; }
      .ve-halo   { paint-order: stroke; stroke: white; stroke-width: 4px; stroke-linejoin: round; }
      .ve-cellt { font-size: 15px; }
      .ve-cellt .ve-math { font-size: 17px; }
      .ve-cellt .ve-sub { font-size: 11px; }
      .ve-legend { font-size: 14px; }
      .ve-legend .ve-math { font-size: 17px; }
      .ve-legend .ve-sub { font-size: 11px; }
    </style>
  </defs>

  <!-- Adversary: receives the revealed value. -->
  <g text-anchor="middle" transform="translate(320,12)">
    <rect class="ve-oracle" width="200" height="62"/>
    <text class="ve-red" x="100" y="24">Adversary 𝒜</text>
    <text x="100" y="52"><tspan class="ve-red"><tspan class="ve-math">r</tspan><tspan class="ve-sub"><tspan class="ve-math">K</tspan></tspan></tspan> <tspan class="ve-muted ve-small">determines dk<tspan class="ve-sub">A</tspan></tspan></text>
  </g>

  <!-- State of A before the send. -->
  <g text-anchor="middle" transform="translate(20,130)">
    <rect class="ve-box" width="160" height="175"/>
    <text x="80" y="22">st<tspan class="ve-sub">A</tspan></text>
    <line class="ve-rule" x1="0" y1="32" x2="160" y2="32"/>
    <text x="80" y="56">dk<tspan class="ve-sub">A</tspan> = ⊥</text>
    <text x="80" y="83">ek<tspan class="ve-sub">A</tspan></text>
    <text x="80" y="110">ct<tspan class="ve-sub">0</tspan></text>
    <text x="80" y="137"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
    <text x="80" y="164">…</text>
  </g>

  <!-- The leaking send samples coins (amber) for its randomized algorithm and returns them. -->
  <g text-anchor="middle" transform="translate(200,96)">
    <rect class="ve-oracle" width="310" height="220"/>
    <text class="ve-red" x="12" y="22" text-anchor="start">O-Send-A-rleak</text>
    <rect class="ve-box" x="36" y="42" width="120" height="44"/>
    <text x="96" y="70">KeyGen</text>
    <rect class="ve-secret" x="196" y="50" width="48" height="28"/>
    <text x="220" y="71"><tspan class="ve-math">r</tspan><tspan class="ve-sub"><tspan class="ve-math">K</tspan></tspan></text>
    <path class="ve-flow" marker-end="url(#vra-arrow)" d="M196 64 H158"/>
    <path class="ve-flow" marker-end="url(#vra-arrow)" d="M96 86 V130"/>
    <text x="96" y="156">(ek<tspan class="ve-sub">A</tspan>, dk<tspan class="ve-sub">A</tspan>)</text>
  </g>

  <!-- The coins go to the adversary. -->
  <path class="ve-leak" marker-end="url(#vra-red-arrow)" d="M420 146 V78"/>

  <!-- Vulnerable epochs (hatched) of the revealed value; the oracle adds them to Exposed (red). -->
  <g text-anchor="middle" transform="translate(360,346)">
    <rect class="ve-cell" x="0" y="0" width="40" height="30"/>
    <rect class="ve-vuln" x="40" y="0" width="40" height="30" fill="url(#vra-hatch)"/>
    <rect class="ve-cell" x="80" y="0" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>−1</text>
    <text class="ve-cellt ve-halo" x="60" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
    <text class="ve-cellt" x="100" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>+1</text>
    <path class="ve-flow" marker-end="url(#vra-arrow)" d="M60 32 V60"/>
    <rect class="ve-cell" x="0" y="64" width="40" height="30"/>
    <rect class="ve-exposed" x="40" y="64" width="40" height="30"/>
    <rect class="ve-cell" x="80" y="64" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>−1</text>
    <text class="ve-cellt ve-on-red" x="60" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
    <text class="ve-cellt" x="100" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>+1</text>
    <text x="-12" y="21" text-anchor="end">vuln<tspan class="ve-sub">A</tspan><tspan class="ve-sup" dx="-9">rleak</tspan>(st<tspan class="ve-sub">A</tspan>, <tspan class="ve-math">r</tspan><tspan class="ve-sub"><tspan class="ve-math">K</tspan></tspan>) = {<tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan>}</text>
    <text x="-12" y="85" text-anchor="end">Exposed</text>
  </g>

  <!-- Legend. -->
  <g class="ve-legend" transform="translate(14,459)">
    <rect class="ve-secret" width="22" height="16"/>
    <text x="28" y="13">secret key material of epoch <tspan class="ve-math">t</tspan><tspan class="ve-sub">A</tspan></text>
    <rect class="ve-exposed" x="286" width="22" height="16"/>
    <text x="314" y="13">exposed</text>
    <rect class="ve-vuln" y="24" width="22" height="16" fill="url(#vra-hatch)"/>
    <text x="28" y="37" font-size="13">vulnerable epochs: keys computable by leaking party state or random coins</text>
  </g>
</svg>
"##

/-- Embed the illustration of randomness leakage by A using Verso's SVG renderer. -/
@[directive]
def oppUniKemVulnRleakA : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote oppUniKemVulnRleakASvg) "100%" "\\textwidth" false) #[])

/-- B's leakage vulnerability: `O-Send-B-rleak` runs `Encaps.On(st_ct, ek_A)` with coins `r_1` and
returns `(⊥, r_1)`; in K-PKE `r_1` is the epoch key, so
`vuln^rleak_B(st_B, (⊥, r_1)) = {t_B}`. -/
private def oppUniKemVulnRleakBSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="ve-text" viewBox="0 0 520 506" width="520" height="506" style="display:block;width:100%;height:auto" role="img" aria-label="Randomness leakage by B: O-Send-B-rleak runs Encaps.On on st_ct and ek_A with coins r_1 and returns the randomness (bottom, r_1) to the adversary. In K-PKE, r_1 is the epoch key I_B, so vuln-rleak_B(st_B, (bottom, r_1)) is the set containing t_B, and t_B is added to Exposed.">
  <!--
    Randomness leakage by B: the figure for vuln^rleak_B (online send, r_0 = bottom).
    Units are viewBox pixels. Each block is a group placed by its transform, so its contents use
    local coordinates. Classes: ve-math italic math; ve-sub and ve-sup sub- and superscripts;
    ve-secret secret key material (amber); ve-oracle and ve-leak oracles and values returned to the
    adversary (red); ve-vuln and ve-exposed vulnerable and exposed epochs.
    Layout: adversary top right; state before the send on the left; leaking-send oracle on the right; vulnerable epochs bottom right.
  -->
  <defs>
    <marker id="vrb-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <marker id="vrb-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#b42318" stroke-width="1.2"/></marker>
    <pattern id="vrb-hatch" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <rect width="7" height="7" fill="#fff6e0"/>
      <line x1="0" y1="0" x2="0" y2="7" stroke="#d29a2a" stroke-width="2.2"/>
    </pattern>
    <style>
      .ve-text   { font-family: Arial, Helvetica, sans-serif; font-size: 18px; fill: #171717; }
      .ve-small  { font-size: 14px; }
      .ve-math   { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 21px; }
      .ve-sub    { baseline-shift: -5px; font-size: 14px; }
      .ve-sup    { baseline-shift: 8px; font-size: 12px; }
      .ve-sub .ve-math { font-size: inherit; }
      .ve-red    { fill: #b42318; }
      .ve-muted  { fill: #5f5f5f; }
      .ve-box    { fill: white; stroke: #252525; stroke-width: 1.2; }
      .ve-rule   { stroke: #252525; stroke-width: 1; }
      .ve-oracle { fill: none; stroke: #b42318; stroke-width: 1.4; }
      .ve-secret { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .ve-flow   { fill: none; stroke: #252525; stroke-width: 1.3; }
      .ve-leak   { fill: none; stroke: #b42318; stroke-width: 1.8; }
      .ve-cell   { fill: white; stroke: #8a8a8a; stroke-width: 1; }
      .ve-vuln   { stroke: #b7791f; stroke-width: 1.4; }
      .ve-exposed { fill: #b42318; stroke: #b42318; stroke-width: 1.4; }
      .ve-on-red { fill: white; }
      .ve-halo   { paint-order: stroke; stroke: white; stroke-width: 4px; stroke-linejoin: round; }
      .ve-cellt { font-size: 15px; }
      .ve-cellt .ve-math { font-size: 17px; }
      .ve-cellt .ve-sub { font-size: 11px; }
      .ve-legend { font-size: 14px; }
      .ve-legend .ve-math { font-size: 17px; }
      .ve-legend .ve-sub { font-size: 11px; }
    </style>
  </defs>

  <!-- Adversary: receives the revealed value. -->
  <g text-anchor="middle" transform="translate(320,12)">
    <rect class="ve-oracle" width="200" height="62"/>
    <text class="ve-red" x="100" y="24">Adversary 𝒜</text>
    <text x="100" y="52"><tspan class="ve-red"><tspan class="ve-math">r</tspan><tspan class="ve-sub">1</tspan> = <tspan class="ve-math">I</tspan><tspan class="ve-sub">B</tspan></tspan> <tspan class="ve-muted ve-small">in K-PKE</tspan></text>
  </g>

  <!-- State of B before the send. -->
  <g text-anchor="middle" transform="translate(20,130)">
    <rect class="ve-box" width="160" height="202"/>
    <text x="80" y="22">st<tspan class="ve-sub">B</tspan></text>
    <line class="ve-rule" x1="0" y1="32" x2="160" y2="32"/>
    <text x="80" y="56">ek<tspan class="ve-sub">A</tspan></text>
    <text x="80" y="83">ct<tspan class="ve-sub">0</tspan></text>
    <text x="80" y="110">ct<tspan class="ve-sub">1</tspan> = ⊥</text>
    <rect class="ve-secret" x="16" y="119" width="128" height="24"/>
    <text x="80" y="137">st<tspan class="ve-sub">ct</tspan></text>
    <text x="80" y="164"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
    <text x="80" y="191">…</text>
  </g>

  <!-- The leaking send samples coins (amber) for its randomized algorithm and returns them. -->
  <g text-anchor="middle" transform="translate(200,96)">
    <rect class="ve-oracle" width="310" height="220"/>
    <text class="ve-red" x="12" y="22" text-anchor="start">O-Send-B-rleak</text>
    <rect class="ve-box" x="36" y="42" width="120" height="44"/>
    <text x="96" y="70">Encaps.On</text>
    <rect class="ve-secret" x="196" y="50" width="48" height="28"/>
    <text x="220" y="71"><tspan class="ve-math">r</tspan><tspan class="ve-sub">1</tspan></text>
    <path class="ve-flow" marker-end="url(#vrb-arrow)" d="M196 64 H158"/>
    <path class="ve-flow" marker-end="url(#vrb-arrow)" d="M96 86 V130"/>
    <text x="96" y="156">(ct<tspan class="ve-sub">1</tspan>, <tspan class="ve-math">I</tspan><tspan class="ve-sub">B</tspan>)</text>
    <text class="ve-red ve-small" x="230" y="38" text-anchor="start">(⊥, <tspan class="ve-math">r</tspan><tspan class="ve-sub">1</tspan>)</text>
  </g>

  <!-- Encaps.On reads ek_A and st_ct from the state. -->
  <path class="ve-flow" marker-end="url(#vrb-arrow)" d="M124 180 H210 V152 H234"/>
  <path class="ve-flow" marker-end="url(#vrb-arrow)" d="M164 261 H222 V170 H234"/>

  <!-- The coins go to the adversary. -->
  <path class="ve-leak" marker-end="url(#vrb-red-arrow)" d="M420 146 V78"/>

  <!-- Vulnerable epochs (hatched) of the revealed value; the oracle adds them to Exposed (red). -->
  <g text-anchor="middle" transform="translate(360,346)">
    <rect class="ve-cell" x="0" y="0" width="40" height="30"/>
    <rect class="ve-vuln" x="40" y="0" width="40" height="30" fill="url(#vrb-hatch)"/>
    <rect class="ve-cell" x="80" y="0" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>−1</text>
    <text class="ve-cellt ve-halo" x="60" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
    <text class="ve-cellt" x="100" y="20"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>+1</text>
    <path class="ve-flow" marker-end="url(#vrb-arrow)" d="M60 32 V60"/>
    <rect class="ve-cell" x="0" y="64" width="40" height="30"/>
    <rect class="ve-exposed" x="40" y="64" width="40" height="30"/>
    <rect class="ve-cell" x="80" y="64" width="40" height="30"/>
    <text class="ve-cellt" x="20" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>−1</text>
    <text class="ve-cellt ve-on-red" x="60" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
    <text class="ve-cellt" x="100" y="84"><tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>+1</text>
    <text x="-12" y="21" text-anchor="end">vuln<tspan class="ve-sub">B</tspan><tspan class="ve-sup" dx="-9">rleak</tspan>(st<tspan class="ve-sub">B</tspan>, (⊥, <tspan class="ve-math">r</tspan><tspan class="ve-sub">1</tspan>)) = {<tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan>}</text>
    <text x="-12" y="85" text-anchor="end">Exposed</text>
  </g>

  <!-- Legend. -->
  <g class="ve-legend" transform="translate(14,459)">
    <rect class="ve-secret" width="22" height="16"/>
    <text x="28" y="13">secret key material of epoch <tspan class="ve-math">t</tspan><tspan class="ve-sub">B</tspan></text>
    <rect class="ve-exposed" x="286" width="22" height="16"/>
    <text x="314" y="13">exposed</text>
    <rect class="ve-vuln" y="24" width="22" height="16" fill="url(#vrb-hatch)"/>
    <text x="28" y="37" font-size="13">vulnerable epochs: keys computable by leaking party state or random coins</text>
  </g>
</svg>
"##

/-- Embed the illustration of randomness leakage by B using Verso's SVG renderer. -/
@[directive]
def oppUniKemVulnRleakB : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote oppUniKemVulnRleakBSvg) "100%" "\\textwidth" false) #[])
