/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

open Verso Genre Manual Doc Elab
open Lean

/-- An example adversarial schedule, with per-sender message indices. The SVG
keeps send and receive events separate so delayed and omitted deliveries are
visible. State disclosures and key challenges extend the same trace. -/
private def sckaAdversarySvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" viewBox="-65 0 1030 1035" width="1030" height="1035" style="display:block;width:100%;height:auto" role="img" aria-label="SCKA oracle illustration: the adversary delays A's first message and delivers A's second message first, then corrupts A. A sends a fresh third message. The adversary drops B's first message while retaining its leaked randomness. B's second send derives key I for epoch t; A derives the same key when receiving B's third message. After both outputs, O-Chall(t) returns K, either I or a random key I′, to the adversary in the middle.">
  <defs>
    <marker id="scka-adv-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <marker id="scka-adv-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#b42318" stroke-width="1.2"/></marker>
    <style>
      .sa-text { font-family: Arial, sans-serif; font-size: 18px; fill: #171717; }
      .sa-small { font-size: 15px; }
      .sa-math { font-family: "Times New Roman", serif; font-size: 20px; font-style: italic; }
      .sa-red { fill: #b42318; }
      .sa-oracle { fill: none; stroke: #b42318; stroke-width: 1.3; }
      .sa-algorithm { fill: white; stroke: #252525; stroke-width: 1; }
      .sa-flow { fill: none; stroke: #252525; stroke-width: 1.2; marker-end: url(#scka-adv-arrow); }
      .sa-control { fill: none; stroke: #b42318; stroke-width: 1.4; marker-end: url(#scka-adv-red-arrow); }
    </style>
  </defs>

  <!-- Shared initialization is outside the adversary's view. -->
  <g class="sa-text" text-anchor="middle">
    <text x="145" y="28">Party A</text><text x="755" y="28">Party B</text>
    <rect class="sa-algorithm" x="100" y="46" width="90" height="30"/>
    <text x="145" y="67">Init-A</text>
    <rect class="sa-algorithm" x="390" y="46" width="120" height="30"/>
    <text x="450" y="67">Init-KeyGen</text>
    <rect class="sa-algorithm" x="710" y="46" width="90" height="30"/>
    <text x="755" y="67">Init-B</text>
    <path class="sa-flow" d="M390 61 H190"/><path class="sa-flow" d="M510 61 H710"/>
    <text class="sa-math" x="290" y="53">I</text><text class="sa-math" x="610" y="53">I</text>
  </g>

  <!-- The unfilled central box is the adversarial network. -->
  <rect class="sa-oracle" x="285" y="99" width="330" height="796"/>
  <g class="sa-text sa-red" text-anchor="middle">
    <text x="450" y="125">Adversary 𝒜</text>
  </g>

  <!-- Corrupt A after its second send. A subsequent fresh send allows the
       illustrated epoch to recover before the first challenge. -->
  <path class="sa-control" d="M178 460 H450"/>
  <g class="sa-text" text-anchor="middle">
    <rect class="sa-oracle" x="30" y="416" width="230" height="66"/>
    <text class="sa-red" x="145" y="436">O-Corr-A</text>
    <rect class="sa-algorithm" x="112" y="447" width="66" height="26"/>
    <text x="145" y="466">st<tspan baseline-shift="sub" font-size="13">A</tspan></text>
    <text class="sa-red" x="335" y="448">st<tspan baseline-shift="sub" font-size="13">A</tspan></text>
    <text class="sa-red sa-small" x="450" y="486">A's vulnerable epochs become exposed.</text>
  </g>

  <!-- Local state flows between oracle calls, independently at each party. -->
  <g class="sa-flow">
    <path d="M145 76 V146"/><path d="M145 212 V236"/>
    <path d="M145 302 V416"/><path d="M145 482 V506"/>
    <path d="M145 572 V686"/><path d="M145 752 V776"/>
    <path d="M755 76 V236"/><path d="M755 302 V326"/>
    <path d="M755 392 V506"/><path d="M755 572 V596"/>
    <path d="M755 662 V686"/><path d="M755 752 V776"/>
  </g>
  <g class="sa-text sa-small">
    <text x="155" y="115">st</text><text x="155" y="229">st</text>
    <text x="155" y="365">st</text><text x="155" y="499">st</text>
    <text x="155" y="635">st</text><text x="155" y="769">st</text>
    <text x="765" y="170">st</text><text x="765" y="319">st</text>
    <text x="765" y="455">st</text><text x="765" y="589">st</text>
    <text x="765" y="679">st</text><text x="765" y="769">st</text>
  </g>

  <!-- A sends with fresh randomness after corruption. -->
  <path class="sa-flow" d="M193 550 H707"/>
  <text class="sa-text sa-math" x="450" y="539" text-anchor="middle">ρ<tspan baseline-shift="sub" font-size="14">A,3</tspan></text>

  <!-- A's first message is held until after delivery of its second message.
       The white underlay at the crossing marks two independent paths. -->
  <path class="sa-control" d="M193 190 H432 V370 H707"/>
  <path d="M423 280 H441" fill="none" stroke="white" stroke-width="8"/>
  <path class="sa-flow" d="M193 280 H707"/>
  <g class="sa-text sa-red sa-small">
    <text x="447" y="215">hold</text>
    <text x="447" y="358">deliver second</text>
  </g>
  <g class="sa-text" text-anchor="middle">
    <text class="sa-math" x="337" y="179">ρ<tspan baseline-shift="sub" font-size="14">A,1</tspan></text>
    <text class="sa-math" x="493" y="395">ρ<tspan baseline-shift="sub" font-size="14">A,1</tspan></text>
    <text class="sa-math" x="364" y="266">ρ<tspan baseline-shift="sub" font-size="14">A,2</tspan></text>
    <text class="sa-red sa-small" x="516" y="266">deliver first</text>
  </g>

  <!-- B's first message is visible but never delivered. The leaking send also
       reveals its randomness; there is no fictitious "drop" oracle. -->
  <path class="sa-control" d="M670 640 H398"/>
  <path d="M380 632 L392 648 M392 632 L380 648" fill="none" stroke="#b42318" stroke-width="1.7"/>
  <g class="sa-text" text-anchor="middle">
    <text class="sa-math" x="515" y="627">ρ<tspan baseline-shift="sub" font-size="14">B,1</tspan><tspan class="sa-red">, r</tspan></text>
    <text class="sa-red sa-small" x="450" y="664">drop message; retain randomness</text>
  </g>

  <!-- B's next two messages are delivered; receive indices are per sender. -->
  <path class="sa-flow" d="M707 730 H193"/><path class="sa-flow" d="M707 820 H193"/>
  <g class="sa-text sa-math" text-anchor="middle">
    <text x="450" y="719">ρ<tspan baseline-shift="sub" font-size="14">B,2</tspan></text>
    <text x="450" y="809">ρ<tspan baseline-shift="sub" font-size="14">B,3</tspan></text>
  </g>

  <!-- Red oracle wrappers enclose the original black protocol boxes. -->
  <g class="sa-text" text-anchor="middle">
    <rect class="sa-oracle" x="30" y="146" width="230" height="66"/>
    <text class="sa-red" x="145" y="166">O-Send-A</text>
    <rect class="sa-algorithm" x="97" y="177" width="96" height="26"/>
    <text x="145" y="196">Send-A</text>

    <rect class="sa-oracle" x="30" y="236" width="230" height="66"/>
    <text class="sa-red" x="145" y="256">O-Send-A</text>
    <rect class="sa-algorithm" x="97" y="267" width="96" height="26"/>
    <text x="145" y="286">Send-A</text>

    <rect class="sa-oracle" x="640" y="236" width="230" height="66"/>
    <text class="sa-red" x="755" y="256">O-Rec-B(2)</text>
    <rect class="sa-algorithm" x="707" y="267" width="96" height="26"/>
    <text x="755" y="286">Rec-B</text>

    <rect class="sa-oracle" x="640" y="326" width="230" height="66"/>
    <text class="sa-red" x="755" y="346">O-Rec-B(1)</text>
    <rect class="sa-algorithm" x="707" y="357" width="96" height="26"/>
    <text x="755" y="376">Rec-B</text>

    <rect class="sa-oracle" x="30" y="506" width="230" height="66"/>
    <text class="sa-red" x="145" y="526">O-Send-A</text>
    <rect class="sa-algorithm" x="97" y="537" width="96" height="26"/>
    <text x="145" y="556">Send-A</text>

    <rect class="sa-oracle" x="640" y="506" width="230" height="66"/>
    <text class="sa-red" x="755" y="526">O-Rec-B(3)</text>
    <rect class="sa-algorithm" x="707" y="537" width="96" height="26"/>
    <text x="755" y="556">Rec-B</text>

    <rect class="sa-oracle" x="640" y="596" width="230" height="66"/>
    <text class="sa-red" x="755" y="616">O-Send-B-rleak</text>
    <rect class="sa-algorithm" x="670" y="627" width="170" height="26"/>
    <text x="755" y="646">Send-B-rleak</text>

    <rect class="sa-oracle" x="640" y="686" width="230" height="66"/>
    <text class="sa-red" x="755" y="706">O-Send-B</text>
    <rect class="sa-algorithm" x="707" y="717" width="96" height="26"/>
    <text x="755" y="736">Send-B</text>

    <rect class="sa-oracle" x="30" y="686" width="230" height="66"/>
    <text class="sa-red" x="145" y="706">O-Rec-A(2)</text>
    <rect class="sa-algorithm" x="97" y="717" width="96" height="26"/>
    <text x="145" y="736">Rec-A</text>

    <rect class="sa-oracle" x="640" y="776" width="230" height="66"/>
    <text class="sa-red" x="755" y="796">O-Send-B</text>
    <rect class="sa-algorithm" x="707" y="807" width="96" height="26"/>
    <text x="755" y="826">Send-B</text>

    <rect class="sa-oracle" x="30" y="776" width="230" height="66"/>
    <text class="sa-red" x="145" y="796">O-Rec-A(3)</text>
    <rect class="sa-algorithm" x="97" y="807" width="96" height="26"/>
    <text x="145" y="826">Rec-A</text>
  </g>

  <!-- B derives the key on its first non-leaking send; A derives it later.
       Side outputs remain local, outside the adversary's view. -->
  <path class="sa-flow" d="M803 730 H890"/>
  <path class="sa-flow" d="M97 820 H10"/>
  <g class="sa-text sa-math">
    <text x="895" y="736">(t, I)</text>
    <text x="5" y="826" text-anchor="end">(t, I)</text>
  </g>

  <!-- Challenge the illustrated epoch after both parties derive its key.
       As required by O-Chall, t is unexposed and has not been challenged. -->
  <path class="sa-control" d="M450 950 V878"/>
  <g class="sa-text" text-anchor="middle">
    <text class="sa-red sa-math" x="467" y="926">K</text>
    <rect class="sa-oracle" x="335" y="950" width="230" height="66"/>
    <text class="sa-red" x="450" y="976">O-Chall(t)</text>
    <text class="sa-red" x="450" y="1002"><tspan class="sa-math">K = I</tspan> or random <tspan class="sa-math">I′</tspan></text>
  </g>
</svg>
"##

/-- Embed the SCKA oracle illustration using Verso's SVG renderer, including its
LaTeX export support. -/
@[directive]
def sckaAdversaryIllustration : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote sckaAdversarySvg) "100%" "\\textwidth" false) #[])
