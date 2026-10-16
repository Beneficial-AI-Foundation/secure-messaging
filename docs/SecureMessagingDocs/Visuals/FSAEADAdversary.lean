/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

open Verso Genre Manual Doc Elab
open Lean

/-- An example run of the FS-AEAD game. The adversary delivers the challenge before the
first message, has a forgery rejected while the first message is still in transit, and
corrupts A. After that, a forgery for index 3, which A has not sent yet, is not a win. -/
private def fsaeadAdversarySvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" viewBox="-65 0 1030 1015" width="1030" height="1015" style="display:block;width:100%;height:auto" role="img" aria-label="FS-AEAD oracle illustration: A sends e1 with O-Transmit-A and the challenge e2 with O-Chall-A. O-Corr-B is refused while the challenge is in transit. The adversary delivers e2 first, and O-Deliver-B returns index 2 without the plaintext. A forgery is rejected and record 1 is kept. e1 is delivered late and decrypts to index 1. O-Corr-A reveals A's state and sets corrA, so every index A has not sent yet is compromised. O-Chall-A is then refused. A forgery for index 3 is accepted and is not a win.">
  <defs>
    <marker id="fsaead-adv-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <marker id="fsaead-adv-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#b42318" stroke-width="1.2"/></marker>
    <style>
      .fa-text { font-family: Arial, sans-serif; font-size: 18px; fill: #171717; }
      .fa-small { font-size: 15px; }
      .fa-math { font-family: "Times New Roman", serif; font-size: 20px; font-style: italic; }
      .fa-red { fill: #b42318; }
      .fa-oracle { fill: none; stroke: #b42318; stroke-width: 1.3; }
      .fa-algorithm { fill: white; stroke: #252525; stroke-width: 1; }
      .fa-flow { fill: none; stroke: #252525; stroke-width: 1.2; marker-end: url(#fsaead-adv-arrow); }
      .fa-control { fill: none; stroke: #b42318; stroke-width: 1.4; marker-end: url(#fsaead-adv-red-arrow); }
      .fa-cross { fill: none; stroke: #b42318; stroke-width: 1.7; }
    </style>
  </defs>

  <!-- Key generation and initialization are outside the adversary's view. -->
  <g class="fa-text" text-anchor="middle">
    <text x="145" y="28">Party A</text><text x="755" y="28">Party B</text>
    <rect class="fa-algorithm" x="90" y="46" width="110" height="30"/>
    <text x="145" y="67">FS-Init-S</text>
    <rect class="fa-algorithm" x="400" y="46" width="100" height="30"/>
    <text x="450" y="67">k ←$ 𝒦</text>
    <rect class="fa-algorithm" x="700" y="46" width="110" height="30"/>
    <text x="755" y="67">FS-Init-R</text>
    <path class="fa-flow" d="M400 61 H200"/><path class="fa-flow" d="M500 61 H700"/>
    <text class="fa-math" x="300" y="53">k</text><text class="fa-math" x="600" y="53">k</text>
  </g>

  <!-- The unfilled central box is the adversarial network. -->
  <rect class="fa-oracle" x="285" y="99" width="330" height="856"/>
  <g class="fa-text fa-red" text-anchor="middle">
    <text x="450" y="125">Adversary 𝒜</text>
  </g>

  <!-- Local state flows between oracle calls. B's line skips the refused O-Corr-B. -->
  <g class="fa-flow">
    <path d="M145 76 V146"/><path d="M145 212 V236"/>
    <path d="M145 302 V686"/><path d="M145 752 V776"/>
    <path d="M755 76 V326"/><path d="M755 392 V416"/>
    <path d="M755 482 V506"/><path d="M755 572 V596"/>
    <path d="M755 662 V866"/>
  </g>
  <g class="fa-text fa-small">
    <text x="155" y="115">v<tspan baseline-shift="sub" font-size="12">A</tspan></text>
    <text x="155" y="229">v<tspan baseline-shift="sub" font-size="12">A</tspan></text>
    <text x="155" y="500">v<tspan baseline-shift="sub" font-size="12">A</tspan></text>
    <text x="155" y="769">v<tspan baseline-shift="sub" font-size="12">A</tspan></text>
    <text x="765" y="205">v<tspan baseline-shift="sub" font-size="12">B</tspan></text>
    <text x="765" y="409">v<tspan baseline-shift="sub" font-size="12">B</tspan></text>
    <text x="765" y="499">v<tspan baseline-shift="sub" font-size="12">B</tspan></text>
    <text x="765" y="589">v<tspan baseline-shift="sub" font-size="12">B</tspan></text>
    <text x="765" y="769">v<tspan baseline-shift="sub" font-size="12">B</tspan></text>
  </g>

  <!-- Message 1 is held until after the challenge and the rejected forgery.
       The white underlay at the crossing marks two independent paths. -->
  <path class="fa-control" d="M193 190 H330 V640 H707"/>
  <path d="M321 280 H339" fill="none" stroke="white" stroke-width="8"/>
  <path class="fa-flow" d="M193 280 H420 V460 H707"/>
  <g class="fa-text" text-anchor="middle">
    <text class="fa-math" x="292" y="179">e₁</text>
    <text class="fa-math" x="380" y="269">e₂</text>
  </g>
  <g class="fa-text fa-red fa-small">
    <text x="338" y="215">hold</text>
    <text x="428" y="448">deliver first</text>
    <text x="338" y="628">deliver second</text>
  </g>

  <!-- O-Corr-B is refused while the challenge is in transit. -->
  <path class="fa-control" d="M470 370 H612"/>
  <path class="fa-cross" d="M618 362 L630 378 M630 362 L618 378"/>

  <!-- Return values of the deliveries. The challenge plaintext is not returned. -->
  <g class="fa-text fa-red fa-small" text-anchor="middle">
    <text x="520" y="486">returns (2, ⊥)</text>
    <text x="520" y="666">returns (1, <tspan class="fa-math">m</tspan>)</text>
  </g>

  <!-- A rejected forgery deletes no record (D2), so message 1 still counts as honest. -->
  <path class="fa-control" d="M470 550 H707"/>
  <g class="fa-text" text-anchor="middle">
    <text class="fa-red fa-math" x="560" y="539">e*</text>
    <text class="fa-red fa-small" x="505" y="576">rejected: record 1 kept (D2)</text>
  </g>

  <!-- Corrupting A compromises every index A has not sent yet (D4). -->
  <path class="fa-control" d="M178 730 H450"/>
  <g class="fa-text" text-anchor="middle">
    <text class="fa-red" x="335" y="718">v<tspan baseline-shift="sub" font-size="13">A</tspan></text>
    <text class="fa-red fa-small" x="450" y="756">corrA = true: unsent indices compromised (D4)</text>
  </g>

  <!-- As in Figure 5, A cannot send a challenge while corrupted. -->
  <path class="fa-control" d="M425 813 H284"/>
  <path class="fa-cross" d="M266 805 L278 821 M278 805 L266 821"/>
  <text class="fa-text fa-red fa-small" x="435" y="818">refused: A corrupted</text>

  <!-- A forgery for a compromised index is accepted and is not a win (D4). -->
  <path class="fa-control" d="M470 910 H707"/>
  <g class="fa-text" text-anchor="middle">
    <text class="fa-red fa-small" x="560" y="898"><tspan class="fa-math">e₃</tspan> from <tspan class="fa-math">v</tspan><tspan baseline-shift="sub" font-size="12">A</tspan></text>
    <text class="fa-red fa-small" x="450" y="938">accepts (3, <tspan class="fa-math">m₃</tspan>): 3 not sent yet, no win (D4)</text>
  </g>

  <!-- Red oracle wrappers enclose the black scheme algorithms. -->
  <g class="fa-text" text-anchor="middle">
    <rect class="fa-oracle" x="30" y="146" width="230" height="66"/>
    <text class="fa-red" x="145" y="166">O-Transmit-A(a₁, <tspan class="fa-math">m</tspan>)</text>
    <rect class="fa-algorithm" x="97" y="177" width="96" height="26"/>
    <text x="145" y="196">FS-Send</text>

    <rect class="fa-oracle" x="30" y="236" width="230" height="66"/>
    <text class="fa-red" x="145" y="256">O-Chall-A(a₂, <tspan class="fa-math">m₀, m₁</tspan>)</text>
    <rect class="fa-algorithm" x="97" y="267" width="96" height="26"/>
    <text x="145" y="286">FS-Send</text>

    <rect class="fa-oracle" x="640" y="326" width="230" height="66"/>
    <text class="fa-red" x="755" y="346">O-Corr-B</text>
    <text class="fa-small" x="755" y="378">refused: chall ≠ ∅</text>

    <rect class="fa-oracle" x="640" y="416" width="230" height="66"/>
    <text class="fa-red" x="755" y="436">O-Deliver-B(a₂, e₂)</text>
    <rect class="fa-algorithm" x="707" y="447" width="96" height="26"/>
    <text x="755" y="466">FS-Rcv</text>

    <rect class="fa-oracle" x="640" y="506" width="230" height="66"/>
    <text class="fa-red" x="755" y="526">O-Inject-B(a*, e*)</text>
    <rect class="fa-algorithm" x="707" y="537" width="96" height="26"/>
    <text x="755" y="556">FS-Rcv</text>

    <rect class="fa-oracle" x="640" y="596" width="230" height="66"/>
    <text class="fa-red" x="755" y="616">O-Deliver-B(a₁, e₁)</text>
    <rect class="fa-algorithm" x="707" y="627" width="96" height="26"/>
    <text x="755" y="646">FS-Rcv</text>

    <rect class="fa-oracle" x="30" y="686" width="230" height="66"/>
    <text class="fa-red" x="145" y="706">O-Corr-A</text>
    <rect class="fa-algorithm" x="112" y="717" width="66" height="26"/>
    <text x="145" y="736">v<tspan baseline-shift="sub" font-size="13">A</tspan></text>

    <rect class="fa-oracle" x="30" y="776" width="230" height="66"/>
    <text class="fa-red" x="145" y="815">O-Chall-A</text>

    <rect class="fa-oracle" x="640" y="866" width="230" height="66"/>
    <text class="fa-red" x="755" y="886">O-Inject-B(a₃, e₃)</text>
    <rect class="fa-algorithm" x="707" y="897" width="96" height="26"/>
    <text x="755" y="916">FS-Rcv</text>
  </g>

  <!-- The adversary's guess decides the game, since no win instruction was reached. -->
  <text class="fa-text" x="450" y="992" text-anchor="middle">𝒜 outputs <tspan class="fa-math">b′</tspan>. won = false, so 𝒜 wins if <tspan class="fa-math">b′ = b</tspan>.</text>
</svg>
"##

/-- Embed the FS-AEAD oracle illustration using Verso's SVG renderer, including its
LaTeX export support. -/
@[directive]
def fsaeadAdversaryIllustration : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote fsaeadAdversarySvg) "100%" "\\textwidth" false) #[])
