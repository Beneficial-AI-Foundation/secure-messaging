/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

/-!
# Cryptocode-Style Blocks

Local documentation helpers for cryptocode-style pseudocode and
message-sequence diagrams rendered with KaTeX-compatible TeX plus CSS.

Only the generic cryptocode primitives are defined here. Protocol-specific
shorthand (party names, scheme operations, state symbols) should be added
locally where each protocol is documented.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean

private def smCryptocodeTexPrelude : String :=
r#"
\newcommand{\sample}{\xleftarrow{\$}}
\newcommand{\Return}{\textbf{return}\;}
\newcommand{\req}{\textbf{req}\;}
\newcommand{\getsval}{\gets}

\newcommand{\hdrR}[1]{\textcolor{red}{\textbf{#1}}}
\newcommand{\hdrK}[1]{\textbf{#1}}
\newcommand{\hdrB}[1]{\textcolor{blue}{\textbf{#1}}}
\newcommand{\proc}[2]{\begin{array}{l}#1\\\hline #2\end{array}}
\newcommand{\secdef}[1]{\boxed{\begin{array}{l}#1\end{array}}}

\newcommand{\msgR}[1]{\xrightarrow{\hspace{6em}#1\hspace{6em}}}
\newcommand{\msgL}[1]{\xleftarrow{\hspace{6em}#1\hspace{6em}}}
\newcommand{\cmnt}[1]{\textcolor{gray}{\textsf{#1}}}
\newcommand{\chipK}[1]{\textcolor{red}{#1}}
\newcommand{\chipF}[1]{\textcolor{green}{#1}}
"#

tex_prelude r#"
\newcommand{\sample}{\xleftarrow{\$}}
\newcommand{\Return}{\textbf{return}\;}
\newcommand{\req}{\textbf{req}\;}
\newcommand{\getsval}{\gets}

\newcommand{\hdrR}[1]{\textcolor{red}{\textbf{#1}}}
\newcommand{\hdrK}[1]{\textbf{#1}}
\newcommand{\hdrB}[1]{\textcolor{blue}{\textbf{#1}}}
\newcommand{\proc}[2]{\begin{array}{l}#1\\\hline #2\end{array}}
\newcommand{\secdef}[1]{\boxed{\begin{array}{l}#1\end{array}}}

\newcommand{\msgR}[1]{\xrightarrow{\hspace{6em}#1\hspace{6em}}}
\newcommand{\msgL}[1]{\xleftarrow{\hspace{6em}#1\hspace{6em}}}
\newcommand{\cmnt}[1]{\textcolor{gray}{\textsf{#1}}}
\newcommand{\chipK}[1]{\textcolor{red}{#1}}
\newcommand{\chipF}[1]{\textcolor{green}{#1}}
"#

/-! ## Argument Parsing -/

structure GameCellConfig where
  title : String
  kind : Option String
deriving Inhabited

section
variable [Monad m] [MonadError m]

def GameCellConfig.parse : ArgParse m GameCellConfig :=
  GameCellConfig.mk <$> .positional `title .string <*> .named `kind .string true

instance : FromArgs GameCellConfig m where
  fromArgs := GameCellConfig.parse

end

/-! ## Block Extensions -/

private def attrsWithClass (className : String) : Array (String × String) :=
  #[("class", className)]

private def attrsWithClassAndKind (className : String) (kind? : Option String) :
    Array (String × String) :=
  let attrs := #[("class", className)]
  match kind? with
  | some kind => attrs.push ("data-kind", kind)
  | none => attrs

private def attrValue? (key : String) (attrs : Array (String × String)) : Option String :=
  (attrs.find? (fun attr => attr.1 == key)).map (·.2)

private def hasClass (className : String) (attrs : Array (String × String)) : Bool :=
  match attrValue? "class" attrs with
  | some classes => (classes.splitOn " ").contains className
  | none => false

private def attrsWithLocalTexPrelude (attrs : Array (String × String)) :
    Array (String × String) :=
  (attrs.filter fun attr =>
      attr.1 != "data-bp-tex-prelude-id" && attr.1 != "data-bp-tex-prelude").push
    ("data-bp-tex-prelude", smCryptocodeTexPrelude)

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

block_extension Block.gameGrid where
  data := Json.null
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id _data contents => do
      let body ← contents.mapM goB
      pure <| Verso.Output.Html.tag "div" (attrsWithClass "sm-game-grid")
        (withLocalTexPrelude (.seq body))

block_extension Block.gameCell (title : String) (kind? : Option String) where
  data := toJson (title, kind?)
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id data contents => do
      let (title, kind?) :=
        match fromJson? (α := String × Option String) data with
        | .ok cell => cell
        | .error _ => ("Oracle", none)
      let body ← contents.mapM goB
      pure <| Verso.Output.Html.tag "section"
        (attrsWithClassAndKind "sm-game-cell" kind?) <| .seq #[
          Verso.Output.Html.tag "div" #[
            ("class", "sm-game-cell-header")
          ] (Verso.Output.Html.text true title),
          Verso.Output.Html.tag "div" #[
            ("class", "sm-game-cell-body")
          ] (withLocalTexPrelude (.seq body))
        ]

block_extension Block.msc where
  data := Json.null
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id _data contents => do
      let body ← contents.mapM goB
      pure <| Verso.Output.Html.tag "div" (attrsWithClass "sm-msc")
        (withLocalTexPrelude (.seq body))

/-! ## Directives -/

@[directive]
def gameGrid : DirectiveExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other Block.gameGrid #[$contents,*])

@[directive]
def gameCell : DirectiveExpanderOf GameCellConfig
  | cfg, contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other (Block.gameCell $(quote cfg.title) $(quote cfg.kind)) #[$contents,*])

@[directive]
def msc : DirectiveExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other Block.msc #[$contents,*])
