/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual

/-!
# Message-sequence-chart diagrams (`:::msc`)

A **data-driven** Verso block extension that renders a two-party protocol flow
(Alice/Bob columns, gray `//` comments, coloured algorithm/key chips, and labelled
ping-pong arrows) as editable HTML — no image, no LaTeX/TikZ.

The diagram is described by a small `Msc` value (a list of grid rows; each row is a
left cell, a channel, and a right cell). A generic `render` turns that value into
the HTML the stylesheet expects. To add another protocol flow, write a new `Msc`
literal and a four-line `block_extension` + `@[directive]` that renders it — the
renderer is reused unchanged. This is the minimal, data-driven refinement of a
hand-built HTML transcript: the content is data, not nested markup.

The visual line + arrowhead are pure CSS pseudo-elements (`.sm-cka-wire-line`); the
chip colours are CSS classes. All styling lives in `vb-poc/Main.lean`.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Lean

namespace SMDocs.Msc

/-! ## HTML builders (file-local) -/

private def htxt (s : String) : Verso.Output.Html :=
  Verso.Output.Html.text true s

private def hnode (name : String) (attrs : Array (String × String))
    (children : Array Verso.Output.Html) : Verso.Output.Html :=
  Verso.Output.Html.tag name attrs (.seq children)

private def divc (cls : String) (children : Array Verso.Output.Html) : Verso.Output.Html :=
  hnode "div" #[("class", cls)] children

private def spanc (cls : String) (children : Array Verso.Output.Html) : Verso.Output.Html :=
  hnode "span" #[("class", cls)] children

private def codec (s : String) : Verso.Output.Html :=
  hnode "code" #[] #[htxt s]

/-! ## Data model -/

/-- A chip's role drives its colour: an algorithm name (green), a freshly *generated*
epoch key from a `Send` (blue), or a *derived* epoch key from a `Rec` (red). -/
inductive ChipKind where
  | algo | genKey | derKey
deriving Inhabited

def ChipKind.cls : ChipKind → String
  | .algo => "sm-crypto-chip sm-crypto-chip-comm"
  | .genKey => "sm-crypto-chip sm-crypto-chip-key"
  | .derKey => "sm-crypto-chip sm-crypto-chip-ok"

/-- One token on a code line: literal code text, a coloured chip, or the `←` glyph. -/
inductive Tok where
  | code (s : String)
  | chip (kind : ChipKind) (s : String)
  | assign
deriving Inhabited

/-- One line inside a party cell: a `//` comment, or a sequence of code tokens. -/
inductive Item where
  | comment (s : String)
  | line (toks : Array Tok)
deriving Inhabited

/-- The middle (channel) column of a grid row: a gap, or a labelled arrow. -/
inductive Channel where
  | gap
  | arrowRight (label : String)
  | arrowLeft (label : String)
deriving Inhabited

/-- A grid row: the left party cell, the channel, the right party cell. An empty
item array renders as a spacer rather than a bordered cell. -/
structure GridRow where
  left : Array Item := #[]
  channel : Channel := .gap
  right : Array Item := #[]
deriving Inhabited

/-- A complete message-sequence chart. -/
structure Msc where
  caption : String
  leftParty : String
  rightParty : String
  rows : Array GridRow
deriving Inhabited

/-! ## Generic renderer -/

private def renderTok : Tok → Verso.Output.Html
  | .code s => codec s
  | .chip k s => spanc k.cls #[codec s]
  | .assign => spanc "sm-crypto-assign" #[htxt "←"]

private def renderItem : Item → Verso.Output.Html
  | .comment s => divc "sm-crypto-comment" #[htxt ("// " ++ s)]
  | .line toks => divc "sm-crypto-line" (toks.map renderTok)

private def renderCell (items : Array Item) : Verso.Output.Html :=
  if items.isEmpty then divc "sm-crypto-empty" #[]
  else divc "sm-crypto-cell" (items.map renderItem)

private def renderArrow (dir label : String) : Verso.Output.Html :=
  divc ("sm-crypto-arrow sm-crypto-arrow-" ++ dir) #[
    spanc "sm-cka-wire-label" #[codec label],
    spanc "sm-cka-wire-line" #[]
  ]

private def renderChannel : Channel → Verso.Output.Html
  | .gap => divc "sm-crypto-empty" #[]
  | .arrowRight l => renderArrow "right" l
  | .arrowLeft l => renderArrow "left" l

private def renderRow (r : GridRow) : Array Verso.Output.Html :=
  #[renderCell r.left, renderChannel r.channel, renderCell r.right]

/-- Fold an `Msc` value into the `.sm-crypto-flow-grid` HTML the stylesheet expects. -/
def render (m : Msc) : Verso.Output.Html :=
  let header : Array Verso.Output.Html := #[
    spanc "sm-crypto-party" #[htxt m.leftParty],
    spanc "sm-crypto-channel" #[htxt ""],
    spanc "sm-crypto-party sm-crypto-party-right" #[htxt m.rightParty]
  ]
  let cells := m.rows.foldl (init := header) (fun acc r => acc ++ renderRow r)
  hnode "figure" #[("class", "sm-cryptocode sm-crypto-flow"), ("aria-label", m.caption)] #[
    hnode "figcaption" #[("class", "sm-crypto-caption")] #[htxt m.caption],
    divc "sm-crypto-flow-grid" cells
  ]

end SMDocs.Msc

/-! ## The CKA protocol transcript (the showcase instance)

Reproduces the Diffie-Hellman CKA ping-pong: each epoch key is *generated* by one
party's `Send` (blue chip) and *derived* by the peer's `Rec` (red chip); the four
protocol messages `ρ₁…ρ₄` alternate direction. The chip names mirror the real
`CKAScheme` fields (`initA`, `sendA`, `recvB`, …). -/

open SMDocs.Msc in
private def ckaMsc : SMDocs.Msc.Msc where
  caption := "Continuous key agreement: each epoch key is generated by one party and derived by the other"
  leftParty := "Alice(I_CKA)"
  rightParty := "Bob(I_CKA)"
  rows := #[
    -- initialise both parties
    { left := #[
        .comment "generate initial state",
        .line #[.code "st_A", .assign, .chip .algo "Init-A(I_CKA)"] ],
      channel := .gap,
      right := #[
        .comment "generate initial state",
        .line #[.code "st_B", .assign, .chip .algo "Init-B(I_CKA)"] ] },
    -- Alice sends ρ₁ (generates K₁); Bob receives it (derives K₁) then sends ρ₂ (generates K₂)
    { left := #[
        .comment "generate new key and message",
        .line #[.code "(", .chip .genKey "K₁", .code ", ρ₁, st_A)", .assign, .chip .algo "Send-A(st_A)"] ],
      channel := .arrowRight "ρ₁",
      right := #[
        .comment "derive shared key K₁",
        .line #[.code "(", .chip .derKey "K₁", .code ", st_B)", .assign, .chip .algo "Rec-B(st_B, ρ₁)"],
        .comment "generate new key and message",
        .line #[.code "(", .chip .genKey "K₂", .code ", ρ₂, st_B)", .assign, .chip .algo "Send-B(st_B)"] ] },
    -- ρ₂ travels back to Alice
    { channel := .arrowLeft "ρ₂" },
    -- Alice receives ρ₂ (derives K₂) then sends ρ₃ (generates K₃); Bob receives ρ₃ (derives K₃), sends ρ₄ (K₄)
    { left := #[
        .comment "derive shared key K₂",
        .line #[.code "(", .chip .derKey "K₂", .code ", st_A)", .assign, .chip .algo "Rec-A(st_A, ρ₂)"],
        .comment "generate new key and message",
        .line #[.code "(", .chip .genKey "K₃", .code ", ρ₃, st_A)", .assign, .chip .algo "Send-A(st_A)"] ],
      channel := .arrowRight "ρ₃",
      right := #[
        .comment "derive shared key K₃",
        .line #[.code "(", .chip .derKey "K₃", .code ", st_B)", .assign, .chip .algo "Rec-B(st_B, ρ₃)"],
        .comment "generate new key and message",
        .line #[.code "(", .chip .genKey "K₄", .code ", ρ₄, st_B)", .assign, .chip .algo "Send-B(st_B)"] ] },
    -- ρ₄ travels back to Alice, who derives K₄
    { left := #[
        .comment "derive shared key K₄",
        .line #[.code "(", .chip .derKey "K₄", .code ", st_A)", .assign, .chip .algo "Rec-A(st_A, ρ₄)"] ],
      channel := .arrowLeft "ρ₄" }
  ]

/-! ## Block extension + directive

`:::msc` renders the CKA transcript. The renderer (`SMDocs.Msc.render`) is generic;
a second diagram needs only a new `Msc` value and a copy of these two declarations. -/

block_extension Block.msc where
  data := Json.null
  traverse _id _data _contents := do
    pure none
  toTeX :=
    some <| fun _goI _goB _id _data _contents => do
      pure <| Verso.Output.TeX.raw
        "\\paragraph{CKA protocol flow.} (Rendered as an HTML message-sequence chart in web output.)\n"
  toHtml :=
    some <| fun _goI _goB _id _data _contents => do
      pure (SMDocs.Msc.render ckaMsc)

@[directive]
def msc : DirectiveExpanderOf Unit
  | (), _contents => do
    ``(Block.other Block.msc #[])
