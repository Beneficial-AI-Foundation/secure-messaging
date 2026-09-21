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
visible. Security-oracle replies are distinguished from ordinary public replies. -/
private def sckaAdversarySvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 900 910" width="900" height="910" style="display:block;width:100%;height:auto" role="img" aria-label="SCKA oracle illustration: the adversary delays A's first message, delivers A's second message first, and drops B's first message. Red boxes wrap the protocol operations in adversarially scheduled oracle calls. Security calls can additionally reveal randomness, local states, or a real-or-random challenge key.">
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
  <rect class="sa-oracle" x="285" y="99" width="330" height="607"/>
  <g class="sa-text sa-red" text-anchor="middle">
    <text x="450" y="125">Adversary 𝒜</text>
    <text class="sa-small" x="450" y="147">stores messages; chooses oracle calls</text>
  </g>

  <!-- Local state flows between oracle calls, independently at each party. -->
  <g class="sa-flow">
    <path d="M145 76 V146"/><path d="M145 212 V236"/>
    <path d="M145 302 V506"/><path d="M145 572 V596"/>
    <path d="M755 76 V236"/><path d="M755 302 V326"/>
    <path d="M755 392 V416"/><path d="M755 482 V506"/>
    <path d="M755 572 V596"/>
  </g>
  <g class="sa-text sa-small">
    <text x="155" y="115">st</text><text x="155" y="229">st</text>
    <text x="155" y="410">st</text><text x="155" y="589">st</text>
    <text x="765" y="176">st</text><text x="765" y="319">st</text>
    <text x="765" y="409">st</text><text x="765" y="499">st</text>
    <text x="765" y="589">st</text>
  </g>

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
  <path class="sa-control" d="M670 460 H398"/>
  <path d="M380 452 L392 468 M392 452 L380 468" fill="none" stroke="#b42318" stroke-width="1.7"/>
  <g class="sa-text" text-anchor="middle">
    <text class="sa-math" x="515" y="447">ρ<tspan baseline-shift="sub" font-size="14">B,1</tspan><tspan class="sa-red">, r</tspan></text>
    <text class="sa-red sa-small" x="450" y="484">drop message; retain randomness</text>
    <text class="sa-red sa-small" x="450" y="504">no O-Rec-A(1) call</text>
  </g>

  <!-- B's next two messages are delivered; receive indices are per sender. -->
  <path class="sa-flow" d="M707 550 H193"/><path class="sa-flow" d="M707 640 H193"/>
  <g class="sa-text sa-math" text-anchor="middle">
    <text x="450" y="539">ρ<tspan baseline-shift="sub" font-size="14">B,2</tspan></text>
    <text x="450" y="629">ρ<tspan baseline-shift="sub" font-size="14">B,3</tspan></text>
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

    <rect class="sa-oracle" x="640" y="416" width="230" height="66"/>
    <text class="sa-red" x="755" y="436">O-Send-B-rleak</text>
    <rect class="sa-algorithm" x="670" y="447" width="170" height="26"/>
    <text x="755" y="466">Send-B-rleak</text>

    <rect class="sa-oracle" x="640" y="506" width="230" height="66"/>
    <text class="sa-red" x="755" y="526">O-Send-B</text>
    <rect class="sa-algorithm" x="707" y="537" width="96" height="26"/>
    <text x="755" y="556">Send-B</text>

    <rect class="sa-oracle" x="30" y="506" width="230" height="66"/>
    <text class="sa-red" x="145" y="526">O-Rec-A(2)</text>
    <rect class="sa-algorithm" x="97" y="537" width="96" height="26"/>
    <text x="145" y="556">Rec-A</text>

    <rect class="sa-oracle" x="640" y="596" width="230" height="66"/>
    <text class="sa-red" x="755" y="616">O-Send-B</text>
    <rect class="sa-algorithm" x="707" y="627" width="96" height="26"/>
    <text x="755" y="646">Send-B</text>

    <rect class="sa-oracle" x="30" y="596" width="230" height="66"/>
    <text class="sa-red" x="145" y="616">O-Rec-A(3)</text>
    <rect class="sa-algorithm" x="97" y="627" width="96" height="26"/>
    <text x="145" y="646">Rec-A</text>
  </g>

  <text class="sa-text sa-red sa-small" x="450" y="691" text-anchor="middle">𝒜 sees messages and returned epoch indices.</text>

  <!-- This legend describes possible disclosures, not extra calls in the trace.
       In particular, it does not challenge an epoch exposed by the leaking send. -->
  <g class="sa-text" text-anchor="middle">
    <text class="sa-red" x="450" y="752">Security-oracle replies (subject to their req checks)</text>
    <rect class="sa-oracle" x="15" y="773" width="280" height="110"/>
    <text class="sa-red" x="155" y="796">O-Send-A-rleak</text>
    <text class="sa-red" x="155" y="819">O-Send-B-rleak</text>
    <text class="sa-small" x="155" y="845">Also reveals the randomness</text>
    <text class="sa-small" x="155" y="867">used by that send.</text>

    <rect class="sa-oracle" x="310" y="773" width="280" height="110"/>
    <text class="sa-red" x="450" y="798">O-Corr-A / O-Corr-B</text>
    <text class="sa-small" x="450" y="829">Reveals the selected party’s</text>
    <text class="sa-small" x="450" y="852">current local state.</text>

    <rect class="sa-oracle" x="605" y="773" width="280" height="110"/>
    <text class="sa-red" x="745" y="798">O-Chall(t)</text>
    <text class="sa-small" x="745" y="829">Returns a real or random key</text>
    <text class="sa-small" x="745" y="852">for epoch t.</text>
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
