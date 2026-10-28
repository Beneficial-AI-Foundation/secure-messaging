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

structure LeanCompareConfig where
  caption : String
  left : Option String
  right : Option String
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

def LeanCompareConfig.parse : ArgParse m LeanCompareConfig :=
  LeanCompareConfig.mk <$> .positional `caption .string
    <*> .named `left .string true <*> .named `right .string true

instance : FromArgs LeanCompareConfig m where
  fromArgs := LeanCompareConfig.parse

end

private def mathInline (tex : String) : Verso.Output.Html :=
  bpMathInline tex

/-- Elaborate quoted Lean source with self-contained highlighting so it can be
used inside nested visual directives. -/
@[code_block]
def quotedLean : CodeBlockExpanderOf Unit
  | _, contents => do
    let savedEnv ← getEnv
    let saved := (← getThe DocElabM.State).highlightDeduplicationTable
    modifyThe DocElabM.State fun st => { st with highlightDeduplicationTable := none }
    try
      return (← withOptions (verso.code.warnLineLength.set · 0) <|
        Informal.Lean.elabCommands Informal.Lean.defaultConfig contents).block
    finally
      setEnv savedEnv
      modifyThe DocElabM.State fun st => { st with highlightDeduplicationTable := saved }

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

-- One Lean pill opening two code blocks side by side: the pill row is rendered
-- here (same classes as the rows `smDocsJs` builds), and the first two child
-- blocks become the columns, headed by the optional `left`/`right` labels.
block_extension Block.leanCompare (caption : String) (left right : Option String) where
  data := toJson (caption, left, right)
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id data contents => do
      let (caption, left, right) :=
        match fromJson? (α := String × Option String × Option String) data with
        | .ok cfg => cfg
        | .error _ => ("", none, none)
      let column (label : Option String) (block : Verso.Output.Html) : Verso.Output.Html :=
        let labelHtml := match label with
          | some l => Verso.Output.Html.tag "div" #[("class", "lean-compare-label")]
              (renderPillCaption l)
          | none => .empty
        Verso.Output.Html.tag "div" #[("class", "lean-compare-col")] (.seq #[labelHtml, block])
      let body ← contents.mapM goB
      let cols := body.mapIdx fun i b => column (if i == 0 then left else if i == 1 then right else none) b
      pure <| Verso.Output.Html.tag "div" #[("class", "lean-anchor-row lean-compare")] <| .seq #[
          Verso.Output.Html.tag "div" #[("class", "lean-anchor-head")] <| .seq #[
            Verso.Output.Html.tag "button" #[
                ("type", "button"), ("class", "lean-pill-btn"), ("aria-expanded", "false")
              ] (Verso.Output.Html.text true "Lean"),
            Verso.Output.Html.tag "span" #[("class", "lean-pill-caption")]
              (renderPillCaption caption)
          ],
          Verso.Output.Html.tag "div" #[
              ("class", "lean-anchor-body lean-compare-body"), ("hidden", "")
            ] (.seq cols)
        ]

/-- Place directly above an anchor; text appears after the Lean pill, not on it. -/
@[directive]
def leanPillCaption : DirectiveExpanderOf LeanPillCaptionConfig
  | cfg, _contents => do
    ``(Block.other (Block.leanPillCaption $(quote cfg.caption)) #[])

/-- `:::leanCompare "Caption" (left := "...") (right := "...")` around two anchors: one Lean
pill whose panel shows both side by side, e.g. a definition next to its variant. -/
@[directive]
def leanCompare : DirectiveExpanderOf LeanCompareConfig
  | cfg, contents => do
    let contents ← contents.mapM elabBlock
    ``(Block.other (Block.leanCompare $(quote cfg.caption) $(quote cfg.left) $(quote cfg.right))
        #[$contents,*])

/-- Place inside an atom when no anchor block exists yet, or when the Lean side is partial/planned. -/
@[directive]
def leanPill : DirectiveExpanderOf LeanPillConfig
  | cfg, _contents => do
    ``(Block.other (Block.leanPill $(quote cfg.status)) #[])
