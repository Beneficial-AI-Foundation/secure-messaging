/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoManual.Diagrams

/-! # SPQR epoch diagram

Four chunk streams, two sampling sites, and separate epoch advances.
-/

open Verso Genre Manual Doc Elab
open Lean

/-- An epoch interleaving with acknowledgement carried by vector chunks. -/
private def spqrEpochSvg : String := r##"
<svg xmlns="http://www.w3.org/2000/svg" class="spqr-epoch" viewBox="0 0 640 902"
     width="640" height="902" style="display:block;width:100%;min-width:560px;height:auto"
     role="img" aria-labelledby="spqr-epoch-title spqr-epoch-desc">
  <title id="spqr-epoch-title">One epoch of SPQR</title>
  <desc id="spqr-epoch-desc">
    One successful interleaving in epoch e; streams may overlap. The encapsulation-key sender's
    first send samples key-generation coins, generates a key pair, and sends header chunks tagged
    under the entering authenticator state. The ciphertext sender verifies the decoded header.
    Its first send samples stage-one coins, computes c₁, updates the authenticator, outputs its
    epoch key, and sends c₁ chunks. The first c₁ chunk stops headers; complete c₁ recovery enables
    acknowledgements on vector chunks. On receive, a valid vector and a c₁ acknowledgement enable
    deterministic stage two. The ciphertext sender sends c₂ and tag chunks under the updated
    authenticator state. The first c₂ chunk stops vectors. The encapsulation-key sender decodes,
    decapsulates, updates the authenticator, and verifies the tag. Success outputs its epoch key
    and advances it to e + 1 as ciphertext sender. A later successor-epoch message advances the
    other party to e + 1 as encapsulation-key sender. Only the two marked sends sample coins.
  </desc>
  <defs>
    <marker id="spqr-epoch-arrow" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M1 1 L9 5 L1 9" fill="none" stroke="#245a85" stroke-width="1.5"/>
    </marker>
    <marker id="spqr-epoch-next-arrow" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M1 1 L9 5 L1 9" fill="none" stroke="#555" stroke-width="1.5"/>
    </marker>
    <style>
      .diagram:has(> svg.spqr-epoch) { overflow-x: auto; }
      .spqr-epoch { font-family: Arial, Helvetica, sans-serif; font-size: 15px; fill: #171717; }
      .spqr-epoch .se-heading { font-size: 17px; font-weight: 700; }
      .spqr-epoch .se-bold { font-weight: 700; }
      .spqr-epoch .se-small { font-size: 14px; }
      .spqr-epoch .se-note { font-size: 13px; fill: #555; }
      .spqr-epoch .se-lane { fill: #f3f6f9; stroke: #9aa8b5; stroke-width: 1; }
      .spqr-epoch .se-life { stroke: #aeb9c2; stroke-width: 1.2; stroke-dasharray: 4 5; }
      .spqr-epoch .se-box { fill: white; stroke: #9aa8b5; stroke-width: 1; }
      .spqr-epoch .se-sample { fill: #fff7e5; stroke: #b7791f; stroke-width: 1.4; }
      .spqr-epoch .se-marker { fill: #b7791f; }
      .spqr-epoch .se-number { fill: white; font-size: 12px; font-weight: 700; }
      .spqr-epoch .se-output { fill: #e9f6ed; }
      .spqr-epoch .se-key { fill: #205b34; font-size: 14px; font-weight: 700; }
      .spqr-epoch .se-flow { fill: none; stroke: #245a85; stroke-width: 1.7; }
      .spqr-epoch .se-next { fill: none; stroke: #555; stroke-width: 1.5; stroke-dasharray: 5 4; }
      .spqr-epoch .se-label { font-size: 14px; paint-order: stroke; stroke: white;
        stroke-width: 5px; stroke-linejoin: round; }
      .spqr-epoch .se-barrier { fill: #f1f6fb; stroke: #245a85; stroke-width: 1.4; }
    </style>
  </defs>

  <text class="se-heading" x="20" y="23">One epoch of SPQR</text>
  <text class="se-note" x="20" y="45">
    Epoch e: one successful interleaving; streams may overlap.
  </text>

  <!-- The roles in epoch e. -->
  <rect class="se-lane" x="20" y="64" width="280" height="48" rx="4"/>
  <rect class="se-lane" x="340" y="64" width="280" height="48" rx="4"/>
  <g class="se-bold" text-anchor="middle">
    <text x="160" y="84">Encapsulation-key</text>
    <text x="160" y="103">sender</text>
    <text x="480" y="93">Ciphertext sender</text>
  </g>
  <path class="se-life" d="M160 112 V830 M480 112 V846"/>

  <!-- Sampling site 1 and the authenticated header stream. -->
  <rect class="se-sample" x="20" y="128" width="280" height="64" rx="4"/>
  <circle class="se-marker" cx="38" cy="149" r="9"/>
  <text class="se-number" x="38" y="153" text-anchor="middle">1</text>
  <text class="se-small se-bold" x="54" y="154">Send: sample key-generation coins</text>
  <text x="160" y="177" text-anchor="middle">Generate key pair</text>
  <path class="se-flow" d="M160 218 H480" marker-end="url(#spqr-epoch-arrow)"/>
  <text class="se-label" x="320" y="207" text-anchor="middle">
    Header + tag: entering authenticator state
  </text>
  <rect class="se-box" x="340" y="234" width="280" height="38" rx="4"/>
  <text class="se-small" x="480" y="258" text-anchor="middle">
    Receive: decode and verify header
  </text>

  <!-- Sampling site 2 outputs a key before the vector has arrived. -->
  <rect class="se-sample" x="340" y="286" width="280" height="83" rx="4"/>
  <circle class="se-marker" cx="358" cy="307" r="9"/>
  <text class="se-number" x="358" y="311" text-anchor="middle">2</text>
  <text class="se-small se-bold" x="374" y="312">Send: sample stage-one coins</text>
  <text class="se-small" x="480" y="334" text-anchor="middle">
    Compute c₁; update authenticator
  </text>
  <rect class="se-output" x="354" y="341" width="252" height="22" rx="3"/>
  <text class="se-key" x="480" y="357" text-anchor="middle">Output epoch key</text>
  <path class="se-flow" d="M480 396 H160" marker-end="url(#spqr-epoch-arrow)"/>
  <text class="se-label" x="320" y="385" text-anchor="middle">c₁ chunks</text>
  <text class="se-note" x="20" y="420">First c₁ chunk stops headers</text>

  <!-- Vector chunks acknowledge complete c₁ recovery. -->
  <rect class="se-box" x="20" y="436" width="280" height="48" rx="4"/>
  <text class="se-small" x="160" y="456" text-anchor="middle">
    Receive: recover c₁
  </text>
  <text class="se-note" x="160" y="475" text-anchor="middle">
    Acknowledge on vector chunks
  </text>
  <path class="se-flow" d="M160 510 H480" marker-end="url(#spqr-epoch-arrow)"/>
  <text class="se-label" x="320" y="499" text-anchor="middle">
    Vector chunks + c₁ acknowledgement
  </text>

  <!-- Deterministic stage two runs on receipt of the last prerequisite. -->
  <rect class="se-barrier" x="340" y="526" width="280" height="102" rx="4"/>
  <text class="se-bold" x="480" y="548" text-anchor="middle">Receive: once both hold</text>
  <text class="se-small" x="480" y="571" text-anchor="middle">
    valid vector ∧ c₁ acknowledged
  </text>
  <text x="480" y="594" text-anchor="middle">Compute c₂ and tag</text>
  <text class="se-small" x="480" y="615" text-anchor="middle">
    Tag: updated authenticator state
  </text>
  <path class="se-flow" d="M480 654 H160" marker-end="url(#spqr-epoch-arrow)"/>
  <text class="se-label" x="320" y="643" text-anchor="middle">c₂ + tag chunks</text>
  <text class="se-note" x="20" y="678">First c₂ chunk stops vectors</text>

  <!-- First epoch advance, after decapsulation and tag verification. -->
  <rect class="se-box" x="20" y="694" width="280" height="108" rx="4"/>
  <text class="se-small" x="160" y="716" text-anchor="middle">
    Receive: decode c₂ and tag
  </text>
  <text class="se-small" x="160" y="738" text-anchor="middle">
    Decapsulate; update authenticator; verify
  </text>
  <rect class="se-output" x="34" y="748" width="252" height="22" rx="3"/>
  <text class="se-key" x="160" y="764" text-anchor="middle">
    Success: output epoch key
  </text>
  <text class="se-note" x="160" y="786" text-anchor="middle">
    Enter e + 1 as ciphertext sender
  </text>
  <path class="se-next" d="M160 830 H480" marker-end="url(#spqr-epoch-next-arrow)"/>
  <text class="se-label" x="320" y="819" text-anchor="middle">
    Message of epoch e + 1
  </text>

  <!-- Second epoch advance, on observing a successor-epoch message. -->
  <rect class="se-box" x="340" y="846" width="280" height="42" rx="4"/>
  <text class="se-small" x="480" y="864" text-anchor="middle">Receive successor message</text>
  <text class="se-note" x="480" y="882" text-anchor="middle">
    Enter e + 1 as key sender
  </text>
</svg>
"##

/-- Embed the SPQR epoch diagram. -/
@[directive]
def spqrEpoch : DirectiveExpanderOf Unit
  | (), _ =>
    ``(Block.other
      (Block.diagram $(quote spqrEpochSvg) "100%" "\\textwidth" false) #[])
