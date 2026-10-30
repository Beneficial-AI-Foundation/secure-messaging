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
(`game`/`oracle`/`challenge`/`corrupt`/`security`) selecting the box colour, an
optional `state` (LaTeX) shown right-aligned in the header — the slice of game
state the oracle reads/writes — and an optional `tag` that makes the cell a link
target for `{cellref "tag"}[…]`. -/
structure GameCellConfig where
  title : String
  kind : Option String
  state : Option String
  tag : Option String
deriving Inhabited

/-- Argument of `cellref`: the `tag` of the game cell to link to. -/
structure CellRefConfig where
  tag : String
deriving Inhabited

/-- Arguments of `defTitle`: a Blueprint label and the human-readable name shown
next to that node's "Definition N" heading. -/
structure DefTitleConfig where
  label : String
  title : String
deriving Inhabited

/-- Arguments of `erratum`: the erratum `number`, its `title`, and an optional
`scope` (protocol and figures it concerns) shown right-aligned in the header. -/
structure ErratumConfig where
  number : String
  title : String
  scope : Option String
deriving Inhabited

section
variable [Monad m] [MonadError m]

/-- Parse `gameCell "Title" (kind := "...") (state := "...")` into a `GameCellConfig`. -/
def GameCellConfig.parse : ArgParse m GameCellConfig :=
  GameCellConfig.mk <$> .positional `title .string <*> .named `kind .string true
    <*> .named `state .string true <*> .named `tag .string true

/-- Lets the `gameCell` directive consume its arguments as a `GameCellConfig`. -/
instance : FromArgs GameCellConfig m where
  fromArgs := GameCellConfig.parse

/-- Parse `defTitle "label" "Human title"`. -/
def DefTitleConfig.parse : ArgParse m DefTitleConfig :=
  DefTitleConfig.mk <$> .positional `label .string <*> .positional `title .string

/-- Lets the `defTitle` directive consume its label/title pair. -/
instance : FromArgs DefTitleConfig m where
  fromArgs := DefTitleConfig.parse

/-- Parse `cellref "tag"`. -/
def CellRefConfig.parse : ArgParse m CellRefConfig :=
  CellRefConfig.mk <$> .positional `tag .string

/-- Lets the `cellref` role consume its tag. -/
instance : FromArgs CellRefConfig m where
  fromArgs := CellRefConfig.parse

/-- Parse `erratum "1" "Title" (scope := "...")`. -/
def ErratumConfig.parse : ArgParse m ErratumConfig :=
  ErratumConfig.mk <$> .positional `number .string <*> .positional `title .string
    <*> .named `scope .string true

/-- Lets the `erratum` directive consume its arguments as an `ErratumConfig`. -/
instance : FromArgs ErratumConfig m where
  fromArgs := ErratumConfig.parse

end

/-! ## Block Extensions -/

/-- The Verso domain in which tagged game cells are registered as link targets. -/
def gameCellDomain : Name := `SecureMessagingDocs.gameCell

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
-- (`title` left, optional `state` LaTeX right) and a body of pseudocode. A cell
-- with a `tag` registers itself as a link target (see `cellref`); the first
-- traversal pass records the assigned tag and pins the block's internal id.
block_extension Block.gameCell (title : String) (kind? : Option String) (state? : Option String)
    (tag? : Option String := none) (assignedTag : Option Tag := none) where
  data := toJson (title, kind?, state?, tag?, assignedTag)
  traverse id data contents := do
    match fromJson? (α := String × Option String × Option String × Option String × Option Tag) data with
    | .error e => reportError s!"Error deserializing game cell data: {e}"; pure none
    | .ok (title, kind?, state?, some tag, none) =>
      let path ← (·.path) <$> read
      let assigned ← Verso.Genre.Manual.externalTag id path tag
      modify fun st => st.saveDomainObject gameCellDomain tag id
      pure <| some <| Block.other
        {Block.gameCell title kind? state? (some tag) (some assigned) with id := some id} contents
    | .ok _ => pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB id data contents => do
      let (title, kind?, state?, _, _) :=
        match fromJson? (α := String × Option String × Option String × Option String × Option Tag) data with
        | .ok cell => cell
        | .error _ => ("Oracle", none, none, none, none)
      let xref ← Verso.Doc.Html.HtmlT.state
      let body ← contents.mapM goB
      let titleHtml := Verso.Output.Html.tag "span"
        #[("class", "game-cell-title")] (bpMathInline title)
      let header : Verso.Output.Html :=
        match state? with
        | some s => .seq #[titleHtml, bpMathInline s]
        | none => titleHtml
      pure <| Verso.Output.Html.tag "section"
        (attrsWithClassAndKind "game-cell" kind? ++ xref.htmlId id) <| .seq #[
          Verso.Output.Html.tag "div" #[
            ("class", "game-cell-header")
          ] header,
          Verso.Output.Html.tag "div" #[
            ("class", "game-cell-body")
          ] (withLocalTexPrelude (.seq body))
        ]

-- A numbered erratum box: a `<section class="erratum">` whose header carries the
-- number, title, and optional scope as plain text, and whose body is prose.
block_extension Block.erratum (number title : String) (scope? : Option String) where
  data := toJson (number, title, scope?)
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id data contents => do
      let (number, title, scope?) :=
        match fromJson? (α := String × String × Option String) data with
        | .ok item => item
        | .error _ => ("", "", none)
      let body ← contents.mapM goB
      let numberHtml := Verso.Output.Html.tag "span"
        #[("class", "erratum-number")] (Verso.Output.Html.text true s!"Erratum {number}")
      let titleHtml := Verso.Output.Html.tag "span"
        #[("class", "erratum-title")] (Verso.Output.Html.text true title)
      let header : Verso.Output.Html :=
        match scope? with
        | some scope =>
          .seq #[numberHtml, titleHtml,
            Verso.Output.Html.tag "span" #[("class", "erratum-scope")]
              (Verso.Output.Html.text true scope)]
        | none => .seq #[numberHtml, titleHtml]
      pure <| Verso.Output.Html.tag "section"
        #[("class", "erratum"), ("id", s!"erratum-{number}")] <| .seq #[
          Verso.Output.Html.tag "div" #[("class", "erratum-header")] header,
          Verso.Output.Html.tag "div" #[("class", "erratum-body")]
            (withLocalTexPrelude (.seq body))
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
    ``(Block.other (Block.gameCell $(quote cfg.title) $(quote cfg.kind) $(quote cfg.state) $(quote cfg.tag)) #[$contents,*])

/-- `{cellref "tag"}[text]` — link to the game cell tagged `tag` (possibly on
another page). The site script unfolds the cell when the link is followed. -/
@[role]
def cellref : RoleExpanderOf CellRefConfig
  | cfg, contents => do
    let contents ← contents.mapM Elab.elabInline
    ``(Inline.other (Inline.ref $(quote cfg.tag) (some $(quote gameCellDomain)) none) #[$contents,*])

/-- `:::erratum "1" "Title" (scope := "...")` — a numbered, titled erratum box. -/
@[directive]
def erratum : DirectiveExpanderOf ErratumConfig
  | cfg, contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other (Block.erratum $(quote cfg.number) $(quote cfg.title) $(quote cfg.scope)) #[$contents,*])

/-- `:::defTitle "label" "Name"` — set the name shown beside one Blueprint
definition/theorem number. Keeping this next to the definition makes the title
feel like content while still rendering on the heading line. -/
@[directive]
def defTitle : DirectiveExpanderOf DefTitleConfig
  | cfg, _contents => do
    ``(Block.other (Block.defTitle $(quote cfg.label) $(quote cfg.title)) #[])
