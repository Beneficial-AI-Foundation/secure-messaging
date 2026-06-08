/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-!
# Game and Oracle Boxes

Block extensions and directives for cryptocode-style pseudocode boxes: a
`gameGrid` container holding titled, colour-coded `gameCell` boxes, rendered with
KaTeX plus CSS.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean

/-! ## Argument Parsing -/

/-- Arguments of a `gameCell`: its header `title`, optional `kind`
(`game`/`oracle`/`challenge`/`corrupt`/`security`) selecting the box colour, and an
optional `state` (LaTeX) shown right-aligned in the header — the slice of game
state the oracle reads/writes. -/
structure GameCellConfig where
  title : String
  kind : Option String
  state : Option String
deriving Inhabited

/-- Arguments of `defTitle`: a Blueprint label and the human-readable name shown
next to that node's "Definition N" heading. -/
structure DefTitleConfig where
  label : String
  title : String
deriving Inhabited

structure GithubIssueConfig where
  issue : Nat
deriving Inhabited

section
variable [Monad m] [MonadError m]

/-- Parse `gameCell "Title" (kind := "...") (state := "...")` into a `GameCellConfig`. -/
def GameCellConfig.parse : ArgParse m GameCellConfig :=
  GameCellConfig.mk <$> .positional `title .string <*> .named `kind .string true
    <*> .named `state .string true

/-- Lets the `gameCell` directive consume its arguments as a `GameCellConfig`. -/
instance : FromArgs GameCellConfig m where
  fromArgs := GameCellConfig.parse

/-- Parse `defTitle "label" "Human title"`. -/
def DefTitleConfig.parse : ArgParse m DefTitleConfig :=
  DefTitleConfig.mk <$> .positional `label .string <*> .positional `title .string

/-- Lets the `defTitle` directive consume its label/title pair. -/
instance : FromArgs DefTitleConfig m where
  fromArgs := DefTitleConfig.parse

def GithubIssueConfig.parse : ArgParse m GithubIssueConfig :=
  GithubIssueConfig.mk <$> .positional `issue .nat

instance : FromArgs GithubIssueConfig m where
  fromArgs := GithubIssueConfig.parse

end

/-! ## Block Extensions -/

/-- HTML attributes carrying a single CSS `class`. -/
private def attrsWithClass (className : String) : Array (String × String) :=
  #[("class", className)]

/-- HTML attributes with a CSS `class` plus an optional `data-kind` (used by the
CSS to colour the box). -/
private def attrsWithClassAndKind (className : String) (kind? : Option String) :
    Array (String × String) :=
  let attrs := #[("class", className)]
  match kind? with
  | some kind => attrs.push ("data-kind", kind)
  | none => attrs

/-- Look up an attribute's value by key. -/
private def attrValue? (key : String) (attrs : Array (String × String)) : Option String :=
  (attrs.find? (fun attr => attr.1 == key)).map (·.2)

/-- Whether the `class` attribute contains `className`. -/
private def hasClass (className : String) (attrs : Array (String × String)) : Bool :=
  match attrValue? "class" attrs with
  | some classes => (classes.splitOn " ").contains className
  | none => false

/-- Replace any existing TeX-prelude attributes with our shared `cryptoTexPrelude`. -/
private def attrsWithLocalTexPrelude (attrs : Array (String × String)) :
    Array (String × String) :=
  (attrs.filter fun attr =>
      attr.1 != "data-bp-tex-prelude-id" && attr.1 != "data-bp-tex-prelude").push
    ("data-bp-tex-prelude", cryptoTexPrelude)

/--
Blueprint summary/graph assets can add later empty default TeX preludes. Cryptocode blocks
therefore attach their prelude directly to contained math nodes as a local fallback.
-/
private def withLocalTexPrelude (html : Verso.Output.Html) : Verso.Output.Html :=
  Id.run <| html.visitM (tag := fun name attrs contents => do
    if name == "code" && hasClass "bp_math" attrs then
      pure <| some <| Verso.Output.Html.tag name (attrsWithLocalTexPrelude attrs) contents
    else
      pure none)

-- The grid container: renders its child cells into a `<div class="game-grid">`.
block_extension Block.gameGrid where
  data := Json.null
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id _data contents => do
      let body ← contents.mapM goB
      pure <| Verso.Output.Html.tag "div" (attrsWithClass "game-grid")
        (withLocalTexPrelude (.seq body))

-- A single titled box: a `<section class="game-cell" data-kind=…>` with a header
-- (`title` left, optional `state` LaTeX right) and a body of pseudocode.
block_extension Block.gameCell (title : String) (kind? : Option String) (state? : Option String) where
  data := toJson (title, kind?, state?)
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id data contents => do
      let (title, kind?, state?) :=
        match fromJson? (α := String × Option String × Option String) data with
        | .ok cell => cell
        | .error _ => ("Oracle", none, none)
      let body ← contents.mapM goB
      let titleHtml := Verso.Output.Html.tag "span"
        #[("class", "game-cell-title")] (bpMathInline title)
      let header : Verso.Output.Html :=
        match state? with
        | some s => .seq #[titleHtml, bpMathInline s]
        | none => titleHtml
      pure <| Verso.Output.Html.tag "section"
        (attrsWithClassAndKind "game-cell" kind?) <| .seq #[
          Verso.Output.Html.tag "div" #[
            ("class", "game-cell-header")
          ] header,
          Verso.Output.Html.tag "div" #[
            ("class", "game-cell-body")
          ] (withLocalTexPrelude (.seq body))
        ]

-- A hidden marker that names one Blueprint definition/theorem heading. Site JS
-- moves this into the actual heading row so the title is normal selectable text.
block_extension Block.defTitle (label title : String) where
  data := toJson (label, title)
  traverse _id _data _contents := do
    pure none
  toTeX := none
  toHtml :=
    some <| fun _goI _goB _id data _contents => do
      let (label, title) :=
        match fromJson? (α := String × String) data with
        | .ok item => item
        | .error _ => ("", "")
      pure <| Verso.Output.Html.tag "span"
        #[
          ("class", "bp-heading-title-marker"),
          ("data-label", label),
          ("data-title", title)
        ]
        (Verso.Output.Html.text true "")

/-! ## Directives -/

/-- `:::gameGrid` — open a grid of game cells. -/
@[directive]
def gameGrid : DirectiveExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other Block.gameGrid #[$contents,*])

/-- `:::gameCell "Title" (kind := "...")` — a single titled box inside a grid. -/
@[directive]
def gameCell : DirectiveExpanderOf GameCellConfig
  | cfg, contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other (Block.gameCell $(quote cfg.title) $(quote cfg.kind) $(quote cfg.state)) #[$contents,*])

/-- `:::defTitle "label" "Name"` — set the name shown beside one Blueprint
definition/theorem number. Keeping this next to the definition makes the title
feel like content while still rendering on the heading line. -/
@[directive]
def defTitle : DirectiveExpanderOf DefTitleConfig
  | cfg, _contents => do
    ``(Block.other (Block.defTitle $(quote cfg.label) $(quote cfg.title)) #[])

/-! ## Dependency ("uses") label

The `{usesLabel}` role renders the small muted label that introduces a node's
dependency list, matching the "used by" chip font in the heading. -/

-- Wraps its content in a `<span class="uses-label">` styled like the heading chip.
inline_extension Inline.usesLabel where
  data := Json.null
  traverse _id _data _contents := do
    pure none
  toTeX := none
  toHtml :=
    some <| fun goI _id _data contents => do
      let inner ← contents.mapM goI
      pure <| Verso.Output.Html.tag "span" (attrsWithClass "uses-label") (.seq inner)

/-- usesLabel role: inline label introducing a dependency list. -/
@[role]
def usesLabel : RoleExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM Elab.elabInline
    ``(Inline.other Inline.usesLabel #[$contents,*])

/-! ## GitHub issue links

The `{githubLabel}` role and `{githubIssue N}` role render a compact footer for
issue links, matching the dependency label style used by `{usesLabel}`. -/

inline_extension Inline.githubLabel where
  data := Json.null
  traverse _id _data _contents := do
    pure none
  toTeX := none
  toHtml :=
    some <| fun goI _id _data contents => do
      let inner ← contents.mapM goI
      pure <| Verso.Output.Html.tag "span" (attrsWithClass "uses-label github-label") (.seq inner)

inline_extension Inline.githubIssue (issue : Nat) where
  data := toJson issue
  traverse _id _data _contents := do
    pure none
  toTeX := none
  toHtml :=
    some <| fun _goI _id data _contents => do
      let issue :=
        match fromJson? (α := Nat) data with
        | .ok n => n
        | .error _ => 0
      let issueText := s!"#{issue}"
      let href := s!"https://github.com/Beneficial-AI-Foundation/secure-messaging/issues/{issue}"
      pure <| Verso.Output.Html.tag "a"
        #[("class", "github-issue-link"), ("href", href), ("target", "_blank"), ("rel", "noopener noreferrer")]
        (Verso.Output.Html.text true issueText)

/-- githubLabel role: inline label introducing GitHub issue links. -/
@[role]
def githubLabel : RoleExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM Elab.elabInline
    ``(Inline.other Inline.githubLabel #[$contents,*])

/-- githubIssue role: compact link to one repository issue, e.g. `{githubIssue 123}[]`. -/
@[role]
def githubIssue : RoleExpanderOf GithubIssueConfig
  | cfg, _contents => do
    ``(Inline.other (Inline.githubIssue $(quote cfg.issue)) #[])
