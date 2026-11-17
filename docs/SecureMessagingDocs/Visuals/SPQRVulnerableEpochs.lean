/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import VersoManual.Diagrams

/-! # SPQR vulnerable epochs illustration
The authenticator state entering an epoch, its update with the epoch key into the state entering
the next epoch, the corruptions and leaking sends that reveal each of them, and the epochs each
exposes. The colours follow the Opp-UniKEM vulnerable-epoch figures. -/

open Verso Genre Manual Doc Elab
open Lean

/-- The authenticator chain `a_ep → a_{ep+1}` updated with the epoch key `k_ep`, under the key-hiding
principle: corrupting states 1 to 7 reveals `a_ep` and exposes `ep`, corrupting states 8 to 10
reveals `a_{ep+1}` and exposes `ep + 1`, and the key material of `ep` exposes both. -/
private def spqrVulnerableEpochsSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="ve-text" viewBox="0 0 1000 400" width="1000" height="400" style="display:block;width:100%;max-width:1000px;height:auto;margin:0 auto" role="img" aria-labelledby="spqr-vuln-title spqr-vuln-desc">
  <title id="spqr-vuln-title">SPQR exposures along the authenticator chain</title>
  <desc id="spqr-vuln-desc">Key hiding protects the epoch key k_e only while the authenticator state a_e entering e, and the key a_e is derived from, stay hidden. The state a_ep is updated with k_ep into a_ep+1. Corrupting states 1 to 7 reveals auth, which is a_ep, and exposes ep. Corrupting states 8 to 10 reveals auth, which is a_ep+1 since it is already updated with k_ep, and exposes ep+1. Corrupting states 2 to 5 or 8 to 9b, or a leaking send from state 1 or 7, reveals key material of ep (sk, encapsSt, r_K, or r_1) and exposes ep, and also ep+1 since a_ep+1 is derived from k_ep.</desc>
  <defs>
    <marker id="spqr-vuln-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <style>
      .ve-text   { font-family: Arial, Helvetica, sans-serif; font-size: 18px; fill: #171717; }
      .ve-small  { font-size: 15px; }
      .ve-math   { font-family: "Times New Roman", Times, serif; font-style: italic; font-size: 21px; }
      .ve-small .ve-math { font-size: 18px; }
      .ve-sub    { baseline-shift: -5px; font-size: 14px; }
      .ve-small .ve-sub { font-size: 12px; }
      .ve-muted  { fill: #5f5f5f; }
      .ve-box    { fill: white; stroke: #252525; stroke-width: 1.2; }
      .ve-secret { fill: #fff6e0; stroke: #b7791f; stroke-width: 1.8; }
      .ve-flow   { fill: none; stroke: #252525; stroke-width: 1.3; }
      .ve-cell   { fill: white; stroke: #8a8a8a; stroke-width: 1; }
      .ve-exposed { fill: #b42318; stroke: #b42318; stroke-width: 1.4; }
      .ve-on-red { fill: white; }
      .ve-cellt  { font-size: 15px; }
      .ve-legend { font-size: 14px; }
    </style>
  </defs>

  <!-- The principle: key hiding protects k_e only while a_e and the key it is derived from are hidden. -->
  <text class="ve-small ve-muted" x="500" y="22" text-anchor="middle">Key hiding protects <tspan class="ve-math">k</tspan><tspan class="ve-sub">e</tspan> only while <tspan class="ve-math">a</tspan><tspan class="ve-sub">e</tspan>, and the key <tspan class="ve-math">a</tspan><tspan class="ve-sub">e</tspan> is derived from, stay hidden.</text>

  <!-- The chain: a_ep is updated with k_ep into a_{ep+1}. -->
  <rect class="ve-box" x="110" y="52" width="120" height="48" rx="4"/>
  <text x="170" y="84" text-anchor="middle"><tspan class="ve-math">a</tspan><tspan class="ve-sub">ep</tspan></text>
  <rect class="ve-box" x="770" y="52" width="120" height="48" rx="4"/>
  <text x="830" y="84" text-anchor="middle"><tspan class="ve-math">a</tspan><tspan class="ve-sub">ep+1</tspan></text>
  <path class="ve-flow" marker-end="url(#spqr-vuln-arrow)" d="M230 76 H768"/>
  <text x="500" y="64" text-anchor="middle">Update(·, ep, <tspan class="ve-math">k</tspan><tspan class="ve-sub">ep</tspan>)</text>
  <rect class="ve-secret" x="450" y="118" width="100" height="40" rx="4"/>
  <text x="500" y="145" text-anchor="middle"><tspan class="ve-math">k</tspan><tspan class="ve-sub">ep</tspan></text>
  <path class="ve-flow" marker-end="url(#spqr-vuln-arrow)" d="M500 118 V78"/>

  <!-- What reveals each value. -->
  <g class="ve-small" text-anchor="middle">
    <text x="170" y="128">corrupting states 1 to 7</text>
    <text x="170" y="150">reveals auth = <tspan class="ve-math">a</tspan><tspan class="ve-sub">ep</tspan></text>

    <text x="830" y="128">corrupting states 8 to 10</text>
    <text x="830" y="150">reveals auth = <tspan class="ve-math">a</tspan><tspan class="ve-sub">ep+1</tspan>,</text>
    <text x="830" y="172">already updated with <tspan class="ve-math">k</tspan><tspan class="ve-sub">ep</tspan></text>

    <text x="500" y="184">corrupting states 2 to 5 (sk) or 8 to 9b (encapsSt),</text>
    <text x="500" y="206">or a leaking send from state 1 (<tspan class="ve-math">r</tspan><tspan class="ve-sub">K</tspan>) or 7 (<tspan class="ve-math">r</tspan><tspan class="ve-sub">1</tspan>),</text>
    <text x="500" y="228">reveals key material of ep</text>
  </g>

  <!-- The epochs each value exposes. -->
  <text class="ve-muted" x="24" y="282">exposes</text>
  <g text-anchor="middle" class="ve-cellt">
    <rect class="ve-exposed" x="114" y="262" width="56" height="30"/>
    <rect class="ve-cell" x="170" y="262" width="56" height="30"/>
    <text class="ve-on-red" x="142" y="282">ep</text>
    <text x="198" y="282">ep+1</text>

    <rect class="ve-exposed" x="444" y="262" width="56" height="30"/>
    <rect class="ve-exposed" x="500" y="262" width="56" height="30"/>
    <text class="ve-on-red" x="472" y="282">ep</text>
    <text class="ve-on-red" x="528" y="282">ep+1</text>

    <rect class="ve-cell" x="774" y="262" width="56" height="30"/>
    <rect class="ve-exposed" x="830" y="262" width="56" height="30"/>
    <text x="802" y="282">ep</text>
    <text class="ve-on-red" x="858" y="282">ep+1</text>
  </g>
  <text class="ve-small ve-muted" x="500" y="318" text-anchor="middle">ep + 1 too, since <tspan class="ve-math">a</tspan><tspan class="ve-sub">ep+1</tspan> is derived from <tspan class="ve-math">k</tspan><tspan class="ve-sub">ep</tspan></text>

  <!-- Legend. -->
  <g class="ve-legend" transform="translate(24,362)">
    <rect class="ve-secret" width="22" height="16"/>
    <text x="30" y="13">key material of epoch ep</text>
    <rect class="ve-exposed" x="250" width="22" height="16"/>
    <text x="280" y="13">exposed epoch</text>
  </g>
</svg>
"##

/-- Embed the illustration of SPQR's exposures along the authenticator chain. -/
@[directive]
def spqrVulnerableEpochs : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote spqrVulnerableEpochsSvg) "100%" "\\textwidth" false) #[])
