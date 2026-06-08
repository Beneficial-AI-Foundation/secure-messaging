/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean

structure LeanPillCaptionConfig where
  caption : String
deriving Inhabited

structure LeanPillConfig where
  status : String
deriving Inhabited

section
variable [Monad m] [MonadError m]

def LeanPillCaptionConfig.parse : ArgParse m LeanPillCaptionConfig :=
  LeanPillCaptionConfig.mk <$> .positional `caption .string

instance : FromArgs LeanPillCaptionConfig m where
  fromArgs := LeanPillCaptionConfig.parse

def LeanPillConfig.parse : ArgParse m LeanPillConfig :=
  LeanPillConfig.mk <$> .positional `status .string

instance : FromArgs LeanPillConfig m where
  fromArgs := LeanPillConfig.parse

end

private def mathInline (tex : String) : Verso.Output.Html :=
  bpMathInline tex

/-- Render caption text plus `$`…` inline math (same syntax as Verso prose). -/
partial def renderPillCaption.go (s : String) (acc : Array Verso.Output.Html) : Verso.Output.Html :=
  if s.isEmpty then
    Verso.Output.Html.seq acc
  else
    match s.find? "$`" with
    | none => Verso.Output.Html.seq (acc.push (Verso.Output.Html.text true s))
    | some openPos =>
      let before := s.extract s.startPos openPos
      let tail := s.extract openPos s.endPos
      let acc' := if before.isEmpty then acc else acc.push (Verso.Output.Html.text true before)
      match tail.dropPrefix? "$`" with
      | none => Verso.Output.Html.seq (acc'.push (Verso.Output.Html.text true s))
      | some afterSlice =>
        let after := afterSlice.copy
        match after.find? "`" with
        | none => Verso.Output.Html.seq (acc'.push (Verso.Output.Html.text true s))
        | some closePos =>
          let tex := after.extract after.startPos closePos
          let rest :=
            (after.extract closePos after.endPos).dropPrefix? "`" |>.map (·.copy) |>.getD ""
          renderPillCaption.go rest (acc'.push (mathInline tex))

def renderPillCaption (caption : String) : Verso.Output.Html :=
  renderPillCaption.go caption #[]

block_extension Block.leanPillCaption (caption : String) where
  data := toJson caption
  traverse _id _data _contents := do
    pure none
  toTeX := none
  toHtml :=
    some <| fun _goI _goB _id data _contents => do
      let caption :=
        match fromJson? (α := String) data with
        | .ok s => s
        | .error _ => ""
      pure <| Verso.Output.Html.tag "p" #[("class", "lean-pill-caption")] <|
        renderPillCaption caption

block_extension Block.leanPill (status : String) where
  data := toJson status
  traverse _id _data _contents := do
    pure none
  toTeX := none
  toHtml :=
    some <| fun _goI _goB _id data _contents => do
      let status :=
        match fromJson? (α := String) data with
        | .ok s => s
        | .error _ => "missing"
      let caption :=
        match status with
        | "linked" => "Lean"
        | "partial" => "Lean partial"
        | "planned" => "Lean planned"
        | "missing" => "Lean anchor pending"
        | other => s!"Lean {other}"
      let label :=
        match status with
        | "linked" => "Lean"
        | "partial" => "Lean partial"
        | "planned" => "Lean planned"
        | "missing" => "Lean"
        | other => s!"Lean {other}"
      pure <| Verso.Output.Html.tag "div" #[
          ("class", "lean-pill-status"),
          ("data-status", status)
        ] <| .seq #[
          Verso.Output.Html.tag "span" #[("class", "lean-pill-status-label")]
            (Verso.Output.Html.text true label),
          Verso.Output.Html.tag "span" #[("class", "lean-pill-status-caption")]
            (renderPillCaption caption)
        ]

/-- Place directly above an anchor; text appears after the Lean pill, not on it. -/
@[directive]
def leanPillCaption : DirectiveExpanderOf LeanPillCaptionConfig
  | cfg, _contents => do
    ``(Block.other (Block.leanPillCaption $(quote cfg.caption)) #[])

/-- Place inside an atom when no anchor block exists yet, or when the Lean side is partial/planned. -/
@[directive]
def leanPill : DirectiveExpanderOf LeanPillConfig
  | cfg, _contents => do
    ``(Block.other (Block.leanPill $(quote cfg.status)) #[])
