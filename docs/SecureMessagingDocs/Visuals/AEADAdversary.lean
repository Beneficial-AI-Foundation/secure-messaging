/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

open Verso Genre Manual Doc Elab
open Lean

/-- An example run of the one-time IND-CCA game for AEAD. The adversary decrypts before the
challenge, gets the challenge, has a second encryption and the challenge pair refused, and
then decrypts the challenge ciphertext under other associated data. -/
private def aeadAdversarySvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 990 640" width="990" height="640" style="display:block;width:100%;height:auto" role="img" aria-label="AEAD oracle illustration: the game samples K and b. O-Dec(a0, e0) before the challenge returns Dec(K, a0, e0), or bottom if b = 1. O-Enc(a1, m) returns the challenge e*, which is Enc(K, a1, m) if b = 0 and random if b = 1, and sets the challenge pair to (a1, e*). A second O-Enc is refused. O-Dec(a1, e*) is refused because it is the challenge pair. O-Dec(a2, e*) with a2 different from a1 is answered; Figure 1 of ACD19 refuses it. Each call has a query arrow to the oracle and a dashed reply arrow back.">
  <defs>
    <marker id="aead-adv-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#252525" stroke-width="1.2"/></marker>
    <marker id="aead-adv-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 1 1 L 9 5 L 1 9" fill="none" stroke="#b42318" stroke-width="1.2"/></marker>
    <style>
      .ae-text { font-family: Arial, sans-serif; font-size: 18px; fill: #171717; }
      .ae-small { font-size: 15px; }
      .ae-math { font-family: "Times New Roman", serif; font-size: 20px; font-style: italic; }
      .ae-red { fill: #b42318; }
      .ae-oracle { fill: none; stroke: #b42318; stroke-width: 1.3; }
      .ae-algorithm { fill: white; stroke: #252525; stroke-width: 1; }
      .ae-flow { fill: none; stroke: #252525; stroke-width: 1.2; marker-end: url(#aead-adv-arrow); }
      .ae-control { fill: none; stroke: #b42318; stroke-width: 1.4; marker-end: url(#aead-adv-red-arrow); }
      .ae-reply { fill: none; stroke: #b42318; stroke-width: 1.4; stroke-dasharray: 6 4; marker-end: url(#aead-adv-red-arrow); }
      .ae-cross { fill: none; stroke: #b42318; stroke-width: 1.7; }
    </style>
  </defs>

  <!-- Key and challenge bit are sampled outside the adversary's view. -->
  <g class="ae-text" text-anchor="middle">
    <rect class="ae-algorithm" x="560" y="40" width="200" height="34"/>
    <text x="660" y="63">K ←$ 𝒦,  b ←$ {0, 1}</text>
  </g>

  <!-- The key reaches every oracle. -->
  <g class="ae-flow">
    <path d="M660 74 V120"/><path d="M660 186 V210"/><path d="M660 276 V300"/>
    <path d="M660 366 V390"/><path d="M660 456 V480"/>
  </g>
  <text class="ae-text ae-small" x="670" y="102">K</text>

  <!-- The adversary. -->
  <rect class="ae-oracle" x="30" y="99" width="200" height="481"/>
  <text class="ae-text ae-red" x="130" y="125" text-anchor="middle">Adversary 𝒜</text>

  <!-- Each oracle call: a solid query arrow to the oracle and a dashed reply arrow back.
       An X marks a refused query; its reply is ⊥. -->
  <g class="ae-control">
    <path d="M230 143 H520"/><path d="M230 233 H520"/><path d="M230 323 H498"/><path d="M230 413 H498"/><path d="M230 503 H520"/>
  </g>
  <g class="ae-reply">
    <path d="M520 163 H230"/><path d="M520 253 H230"/><path d="M520 343 H230"/><path d="M520 433 H230"/><path d="M520 523 H230"/>
  </g>
  <path class="ae-cross" d="M504 315 L516 331 M516 315 L504 331"/>
  <path class="ae-cross" d="M504 405 L516 421 M516 405 L504 421"/>

  <!-- Replies. -->
  <g class="ae-text ae-red ae-small" text-anchor="middle">
    <text x="375" y="181">Dec(K, a₀, e₀)</text>
    <text x="375" y="199">(⊥ if b = 1)</text>
    <text x="375" y="271"><tspan class="ae-math">e*</tspan></text>
    <text x="375" y="289">(Enc if b = 0, random if b = 1)</text>
    <text x="375" y="361">⊥</text>
    <text x="375" y="451">⊥</text>
    <text x="375" y="541">Dec(K, a₂, <tspan class="ae-math">e*</tspan>)</text>
    <text x="375" y="559">(⊥ if b = 1)</text>
  </g>

  <!-- Red oracle wrappers enclose the black scheme algorithms. -->
  <g class="ae-text" text-anchor="middle">
    <rect class="ae-oracle" x="520" y="120" width="280" height="66"/>
    <text class="ae-red" x="660" y="140">O-Dec(a₀, e₀)</text>
    <rect class="ae-algorithm" x="612" y="151" width="96" height="26"/>
    <text x="660" y="170">Dec</text>

    <rect class="ae-oracle" x="520" y="210" width="280" height="66"/>
    <text class="ae-red" x="660" y="230">O-Enc(a₁, <tspan class="ae-math">m</tspan>)</text>
    <rect class="ae-algorithm" x="545" y="241" width="90" height="26"/>
    <text x="590" y="260">Enc</text>
    <text class="ae-small" x="660" y="259">or</text>
    <rect class="ae-algorithm" x="685" y="241" width="90" height="26"/>
    <text x="730" y="260">←$ 𝒞</text>

    <rect class="ae-oracle" x="520" y="300" width="280" height="66"/>
    <text class="ae-red" x="660" y="320">O-Enc(a₂, <tspan class="ae-math">m′</tspan>)</text>
    <text class="ae-small" x="660" y="352">refused: <tspan class="ae-math">e*</tspan> ≠ ⊥</text>

    <rect class="ae-oracle" x="520" y="390" width="280" height="66"/>
    <text class="ae-red" x="660" y="410">O-Dec(a₁, <tspan class="ae-math">e*</tspan>)</text>
    <text class="ae-small" x="660" y="442">refused: (a, e) = (a*, e*)</text>

    <rect class="ae-oracle" x="520" y="480" width="280" height="66"/>
    <text class="ae-red" x="660" y="500">O-Dec(a₂, <tspan class="ae-math">e*</tspan>)</text>
    <rect class="ae-algorithm" x="612" y="511" width="96" height="26"/>
    <text x="660" y="530">Dec</text>
  </g>

  <!-- Game state after the challenge, and the query that Figure 1 of ACD19 refuses. -->
  <g class="ae-text ae-small">
    <text x="815" y="248">(a*, e*) ← (a₁, <tspan class="ae-math">e*</tspan>)</text>
    <text class="ae-red" x="815" y="508">a₂ ≠ a₁: answered,</text>
    <text class="ae-red" x="815" y="526">ACD19 Figure 1</text>
    <text class="ae-red" x="815" y="544">refuses it</text>
  </g>

  <!-- The adversary's guess decides the game. -->
  <text class="ae-text" x="495" y="618" text-anchor="middle">𝒜 outputs <tspan class="ae-math">b′</tspan> and wins if <tspan class="ae-math">b′ = b</tspan>.</text>
</svg>
"##

/-- Embed the AEAD oracle illustration using Verso's SVG renderer, including its LaTeX export
support. -/
@[directive]
def aeadAdversaryIllustration : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote aeadAdversarySvg) "100%" "\\textwidth" false) #[])
