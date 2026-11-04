/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import VersoManual.Diagrams

/-! # SPQR state diagram
The eleven party states and the thirteen transitions between them, numbered in the order in
which one party visits them: as the encapsulation-key sender of an epoch, then as the ciphertext
sender of the next. -/

open Verso Genre Manual Doc Elab
open Lean

/-- The state machine of one party: each box carries its number, the Lean constructor of the
state with the main values it holds besides the epoch and the authenticator state, and what the
party is doing there; encapsulation-key sender states in blue, ciphertext sender states in green,
`Send` transitions in orange and `Rec` transitions in grey, labelled by the triggering payload. -/
private def spqrStatesSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="spqr-states" viewBox="0 0 1080 478"
     width="1080" height="478" style="display:block;width:100%;min-width:560px;height:auto"
     role="img" aria-labelledby="spqr-states-title spqr-states-desc">
  <title id="spqr-states-title">SPQR party states and transitions</title>
  <desc id="spqr-states-desc">
    A ring of eleven numbered states. As the encapsulation-key sender of an epoch, a party moves
    from 1 keysUnsampled through 2 keysSampled, 3 headerSent, and 4 ct1Received to
    5 ekSentCt1Received; decapsulating ct2 makes it the ciphertext sender of the next epoch at
    6 noHeaderReceived, from which it moves through 7 headerReceived and 8 ct1Sampled to
    10 ct2Sampled, directly when an EkCt1Ack chunk completes ek, or else through 9a
    ct1Acknowledged or 9b ekReceivedCt1Sampled; a message of the
    next epoch returns it to 1. Two transitions are sends that draw coins; the others are
    receives, labelled Rec(payload) by the payload that triggers them.
  </desc>
  <defs>
    <marker id="spqr-states-arrow" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M1 1 L9 5 L1 9" fill="none" stroke="#5b6b7b" stroke-width="1.5"/>
    </marker>
    <marker id="spqr-states-send-arrow" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M1 1 L9 5 L1 9" fill="none" stroke="#b7791f" stroke-width="1.5"/>
    </marker>
    <style>
      .spqr-states text { font-family: ui-sans-serif, system-ui, sans-serif; font-size: 13px;
        fill: #1f2937; }
      .spqr-states .ss-state { font-size: 13px; font-weight: 700; }
      .spqr-states .ss-vars { font-size: 12px; fill: #374151; }
      .spqr-states .ss-meaning { font-size: 11.5px; font-style: italic; fill: #4b5563; }
      .spqr-states .ss-num { font-size: 10.5px; font-weight: 700; fill: #1f2937; }
      .spqr-states .ss-ek { fill: #eef2ff; stroke: #6b7cc4; stroke-width: 1.2; }
      .spqr-states .ss-ct { fill: #ecfdf3; stroke: #4f9d69; stroke-width: 1.2; }
      .spqr-states .ss-badge-ek { fill: #fff; stroke: #6b7cc4; stroke-width: 1.2; }
      .spqr-states .ss-badge-ct { fill: #fff; stroke: #4f9d69; stroke-width: 1.2; }
      .spqr-states .ss-recv { fill: none; stroke: #5b6b7b; stroke-width: 1.4; }
      .spqr-states .ss-send { fill: none; stroke: #b7791f; stroke-width: 1.8; }
      .spqr-states .ss-label { font-size: 11.5px; fill: #374151; }
      .spqr-states .ss-send-label { font-size: 11.5px; fill: #935f10; font-weight: 600; }
      .spqr-states .ss-rec { fill: #1f5f8b; font-weight: 600; }
    </style>
  </defs>

  <!-- States: number, constructor with the values shown, and what the party is doing. -->
  <rect class="ss-ek" x="34" y="24" width="290" height="62" rx="6"/>
  <text x="179" y="50" text-anchor="middle"><tspan class="ss-state">keysUnsampled</tspan></text>
  <text class="ss-meaning" x="179" y="70" text-anchor="middle">epoch opened, no key pair yet</text>
  <circle class="ss-badge-ek" cx="34" cy="24" r="12"/>
  <text class="ss-num" x="34" y="27.5" text-anchor="middle">1</text>
  <rect class="ss-ek" x="396" y="24" width="290" height="62" rx="6"/>
  <text x="541" y="50" text-anchor="middle"><tspan class="ss-state">keysSampled</tspan><tspan class="ss-vars" dx="5">(pk, sk, encoder)</tspan></text>
  <text class="ss-meaning" x="541" y="70" text-anchor="middle">streaming the tagged header of pk</text>
  <circle class="ss-badge-ek" cx="396" cy="24" r="12"/>
  <text class="ss-num" x="396" y="27.5" text-anchor="middle">2</text>
  <rect class="ss-ek" x="758" y="24" width="290" height="62" rx="6"/>
  <text x="903" y="50" text-anchor="middle"><tspan class="ss-state">headerSent</tspan><tspan class="ss-vars" dx="5">(sk, encoder, decoder)</tspan></text>
  <text class="ss-meaning" x="903" y="70" text-anchor="middle">streaming ek, receiving ct1</text>
  <circle class="ss-badge-ek" cx="758" cy="24" r="12"/>
  <text class="ss-num" x="758" y="27.5" text-anchor="middle">3</text>
  <rect class="ss-ek" x="758" y="150" width="290" height="62" rx="6"/>
  <text x="903" y="176" text-anchor="middle"><tspan class="ss-state">ct1Received</tspan><tspan class="ss-vars" dx="5">(sk, ct1, encoder)</tspan></text>
  <text class="ss-meaning" x="903" y="196" text-anchor="middle">streaming ek, acknowledging ct1</text>
  <circle class="ss-badge-ek" cx="758" cy="150" r="12"/>
  <text class="ss-num" x="758" y="153.5" text-anchor="middle">4</text>
  <rect class="ss-ek" x="758" y="276" width="290" height="62" rx="6"/>
  <text x="903" y="302" text-anchor="middle"><tspan class="ss-state">ekSentCt1Received</tspan><tspan class="ss-vars" dx="5">(sk, ct1, decoder)</tspan></text>
  <text class="ss-meaning" x="903" y="322" text-anchor="middle">receiving ct2, acknowledging ct1</text>
  <circle class="ss-badge-ek" cx="758" cy="276" r="12"/>
  <text class="ss-num" x="758" y="279.5" text-anchor="middle">5</text>
  <rect class="ss-ct" x="758" y="402" width="290" height="62" rx="6"/>
  <text x="903" y="428" text-anchor="middle"><tspan class="ss-state">noHeaderReceived</tspan><tspan class="ss-vars" dx="5">(decoder)</tspan></text>
  <text class="ss-meaning" x="903" y="448" text-anchor="middle">receiving the tagged header of pk</text>
  <circle class="ss-badge-ct" cx="758" cy="402" r="12"/>
  <text class="ss-num" x="758" y="405.5" text-anchor="middle">6</text>
  <rect class="ss-ct" x="396" y="402" width="290" height="62" rx="6"/>
  <text x="541" y="428" text-anchor="middle"><tspan class="ss-state">headerReceived</tspan><tspan class="ss-vars" dx="5">(hdr, decoder)</tspan></text>
  <text class="ss-meaning" x="541" y="448" text-anchor="middle">header verified, next send encapsulates</text>
  <circle class="ss-badge-ct" cx="396" cy="402" r="12"/>
  <text class="ss-num" x="396" y="405.5" text-anchor="middle">7</text>
  <rect class="ss-ct" x="34" y="402" width="290" height="62" rx="6"/>
  <text x="179" y="428" text-anchor="middle"><tspan class="ss-state">ct1Sampled</tspan><tspan class="ss-vars" dx="5">(ct1, encoder, decoder)</tspan></text>
  <text class="ss-meaning" x="179" y="448" text-anchor="middle">streaming ct1, receiving ek</text>
  <circle class="ss-badge-ct" cx="34" cy="402" r="12"/>
  <text class="ss-num" x="34" y="405.5" text-anchor="middle">8</text>
  <rect class="ss-ct" x="34" y="276" width="290" height="62" rx="6"/>
  <text x="179" y="302" text-anchor="middle"><tspan class="ss-state">ekReceivedCt1Sampled</tspan><tspan class="ss-vars" dx="5">(ct1, ek, encoder)</tspan></text>
  <text class="ss-meaning" x="179" y="322" text-anchor="middle">ek validated, ct1 not yet acknowledged</text>
  <circle class="ss-badge-ct" cx="34" cy="276" r="12"/>
  <text class="ss-num" x="34" y="279.5" text-anchor="middle">9b</text>
  <rect class="ss-ct" x="396" y="276" width="290" height="62" rx="6"/>
  <text x="541" y="302" text-anchor="middle"><tspan class="ss-state">ct1Acknowledged</tspan><tspan class="ss-vars" dx="5">(ct1, decoder)</tspan></text>
  <text class="ss-meaning" x="541" y="322" text-anchor="middle">ct1 acknowledged, receiving ek</text>
  <circle class="ss-badge-ct" cx="396" cy="276" r="12"/>
  <text class="ss-num" x="396" y="279.5" text-anchor="middle">9a</text>
  <rect class="ss-ct" x="396" y="150" width="290" height="62" rx="6"/>
  <text x="541" y="176" text-anchor="middle"><tspan class="ss-state">ct2Sampled</tspan><tspan class="ss-vars" dx="5">(encoder)</tspan></text>
  <text class="ss-meaning" x="541" y="196" text-anchor="middle">streaming the tagged ct2</text>
  <circle class="ss-badge-ct" cx="396" cy="150" r="12"/>
  <text class="ss-num" x="396" y="153.5" text-anchor="middle">10</text>

  <!-- Transitions: Send in orange, Rec in grey, labelled by the payload that triggers them. -->
  <path class="ss-send" d="M324 55.0 H396" marker-end="url(#spqr-states-send-arrow)"/>
  <text class="ss-send-label" x="360" y="49" text-anchor="middle">Send</text>
  <path class="ss-recv" d="M686 55.0 H758" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="722" y="49" text-anchor="middle"><tspan class="ss-rec">Rec</tspan>(Ct1)</text>
  <path class="ss-recv" d="M903.0 86 V150" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="909" y="122" text-anchor="start"><tspan class="ss-rec">Rec</tspan>(Ct1)</text>
  <path class="ss-recv" d="M903.0 212 V276" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="909" y="248" text-anchor="start"><tspan class="ss-rec">Rec</tspan>(Ct2)</text>
  <path class="ss-recv" d="M903.0 338 V402" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="909" y="374" text-anchor="start"><tspan class="ss-rec">Rec</tspan>(Ct2) · next epoch</text>
  <path class="ss-recv" d="M758 433.0 H686" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="722" y="427" text-anchor="middle"><tspan class="ss-rec">Rec</tspan>(Hdr)</text>
  <path class="ss-send" d="M396 433.0 H324" marker-end="url(#spqr-states-send-arrow)"/>
  <text class="ss-send-label" x="360" y="427" text-anchor="middle">Send</text>
  <path class="ss-recv" d="M179.0 402 V338" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="185" y="374" text-anchor="start"><tspan class="ss-rec">Rec</tspan>(Ek)</text>
  <path class="ss-recv" d="M277.6 402 V370 H686 V338" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="409.3" y="365" text-anchor="middle"><tspan class="ss-rec">Rec</tspan>(EkCt1Ack)</text>
  <path class="ss-recv" d="M179.0 276 V193 H396" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="287.5" y="188" text-anchor="middle"><tspan class="ss-rec">Rec</tspan>(Ct1Ack / EkCt1Ack)</text>
  <path class="ss-recv" d="M541.0 276 V212" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="547" y="248" text-anchor="start"><tspan class="ss-rec">Rec</tspan>(Ek / EkCt1Ack)</text>
  <path class="ss-recv" d="M34 445 H12 V169 H396" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="218" y="164" text-anchor="middle"><tspan class="ss-rec">Rec</tspan>(EkCt1Ack)</text>
  <path class="ss-recv" d="M541.0 150 V118 H179.0 V86" marker-end="url(#spqr-states-arrow)"/>
  <text class="ss-label" x="304" y="132" text-anchor="middle"><tspan class="ss-rec">Rec</tspan>(t = ep+1)</text>
</svg>
"##

/-- Embed the SPQR state diagram. -/
@[directive]
def spqrStates : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote spqrStatesSvg) "100%" "\\textwidth" false) #[])
