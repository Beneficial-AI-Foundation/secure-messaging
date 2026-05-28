/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import SubVerso.Highlighting.String

/-!
# Source Block Helper

Custom Verso helpers for extracting selected source bodies from live Lean
declarations.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean
open SubVerso.Highlighting

/-! ## Local Documentation Blocks -/

structure DocH2Config where
  title : String
deriving Inhabited

section
variable [Monad m] [MonadError m]

def DocH2Config.parse : ArgParse m DocH2Config :=
  DocH2Config.mk <$> .positional `title .string

instance : FromArgs DocH2Config m where
  fromArgs := DocH2Config.parse

end

open Verso Doc Elab Genre Manual in
block_extension Block.docH2 (title : String) where
  data := toJson title
  traverse _id _data _contents := do
    pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String) data with
      | .ok title => pure <| .raw ("\\subsection*{" ++ title ++ "}\n")
      | .error _ => pure .empty
  toHtml :=
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String) data with
      | .ok title =>
        pure <|
          Verso.Output.Html.tag "h2" #[
            ("class", "smdocs-doc-h2"),
            ("style", "margin-top:2.25rem;padding-top:1rem;border-top:1px solid #d8dee8;")
          ]
            (Verso.Output.Html.text true title)
      | .error _ => pure .empty

/--
Renders an HTML `h2`-style heading without creating a Verso section or
Blueprint node.
-/
@[block_command]
meta def docH2 : BlockCommandOf DocH2Config
  | cfg => ``(Block.other (Block.docH2 $(quote cfg.title)) #[])

/-! ## Source Extraction -/

public structure SourceConfig where
  name : Ident
deriving Inhabited

public structure ExtractedSource where
  moduleName : Name
  source : String

instance : FromArgs SourceConfig DocElabM :=
  ⟨SourceConfig.mk <$> positional' (α := Ident) `name⟩

private def findSubstring (haystack needle : String) : Option Nat := Id.run do
  let hLen := haystack.length
  let nLen := needle.length
  if nLen > hLen then
    return none
  for i in [:hLen - nLen + 1] do
    if (haystack.drop i).startsWith needle then
      return some i
  return none

private def isDeclHeaderLine (line : String) : Bool :=
  let line := line.trimAsciiStart.toString
  let isWhereDecl :=
    #["structure ", "class ", "inductive "].any (fun p => line.startsWith p) &&
      line.contains " where"
  let prefixes := #[
    "def ", "noncomputable def ", "private def ", "private noncomputable def ",
    "theorem ", "private theorem ", "lemma ", "private lemma ",
    "abbrev ", "instance ", "opaque ", "axiom "
  ]
  isWhereDecl || prefixes.any (fun p => line.startsWith p)

private def findDeclHeaderStart (lines : List String) (startIdx endLine : Nat) : Nat := Id.run do
  let lines := lines.toArray
  if lines.isEmpty then
    return startIdx
  let start := Nat.min startIdx (lines.size - 1)
  let upper := Nat.min (endLine - 1) (lines.size - 1)
  if start <= upper then
    for idx in [start:upper + 1] do
      if isDeclHeaderLine lines[idx]! then
        return idx
  for offset in [:start + 1] do
    let idx := start - offset
    if isDeclHeaderLine lines[idx]! then
      return idx
  return startIdx

public def extractProofBody (source : String) : String :=
  if let some idx := findSubstring source ":= by" then
    "by" ++ (source.drop (idx + ":= by".length)).toString
  else if (findSubstring source " where").isSome then
    source
  else if let some idx := findSubstring source ":= " then
    (source.drop (idx + ":= ".length)).toString
  else
    source

public meta def extractDeclBody (declName : Name) : DocElabM ExtractedSource := do
  let some ranges ← findDeclarationRanges? declName
    | throwError s!"source: declaration '{declName}' not found or has no source range"

  let env ← getEnv
  let some modIdx := env.getModuleIdxFor? declName
    | throwError s!"source: could not find module for '{declName}'"
  let modName := env.header.moduleNames[modIdx.toNat]!

  let parts := modName.components.map (·.toString)
  let relPath := String.intercalate "/" parts ++ ".lean"
  let candidates : List System.FilePath := [
    relPath,
    ".." / relPath,
    ".." / ".." / relPath
  ]
  let some path ← candidates.findM? (·.pathExists)
    | throwError s!"source: source file not found (tried {candidates})"

  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
  let startLine := ranges.range.pos.line
  let endLine := ranges.range.endPos.line
  let startIdx := findDeclHeaderStart lines (startLine - 1) endLine
  let selected := lines.drop startIdx |>.take (endLine - startIdx)
  let fullSource := "\n".intercalate selected
  pure {
    moduleName := modName
    source := fullSource.trimAscii.toString
  }

private def isPreviewableSource (source : String) : Bool :=
  let source := source.trimAsciiStart.toString
  let prefixes := #[
    "def ", "noncomputable def ", "private def ", "private noncomputable def ",
    "abbrev ", "structure ", "inductive "
  ]
  source.length ≤ 50000 &&
    prefixes.any (source.startsWith ·)

private def isTheoremLikeSource (source : String) : Bool :=
  let source := source.trimAsciiStart.toString
  let prefixes := #[
    "theorem ", "private theorem ", "lemma ", "private lemma "
  ]
  prefixes.any (source.startsWith ·)

private def theoremStatementSource? (source : String) : Option String :=
  let source := source.trimAscii.toString
  let stop? :=
    match findSubstring source ":= by" with
    | some idx => some idx
    | none => findSubstring source ":="
  stop?.map fun idx => (source.take idx).trimAscii.toString

private def sanitizeNamespacePart (s : String) : String :=
  let chars := s.toList.map fun c =>
    if c.isAlphanum then c else '_'
  let s := String.ofList chars
  if s.isEmpty || s.front.isDigit then "decl_" ++ s else s

private def previewNamespace (declName : Name) : String :=
  let parts := declName.components.map (sanitizeNamespacePart ·.toString)
  "SecureMessagingDocs.SourcePreview." ++ String.intercalate "_" parts

private def previewPrefix (_moduleName declName : Name) : String :=
  let ns := previewNamespace declName
  s!"namespace {ns}\n" ++
  "universe u v\n" ++
  "open OracleSpec OracleComp ENNReal\n" ++
  "set_option linter.unusedVariables false\n" ++
  "variable {ι : Type}\n" ++
  "\n"

private def theoremPreviewPrefix (moduleName declName : Name) : String :=
  previewPrefix moduleName declName ++
  "axiom smDocsProof {p : Prop} : p\n\n"

private def previewSuffix (declName : Name) : String :=
  s!"\nend {previewNamespace declName}\n"

private def isSourceStartKeyword (s : String) : Bool :=
  #["private", "noncomputable", "def", "abbrev", "structure", "inductive",
    "theorem", "lemma"].contains s

private def isKeywordLeaf (p : String → Bool) : Highlighted → Bool
  | .token ⟨.keyword .., content⟩ => p content.trimAscii.toString
  | _ => false

private def isAnyKeywordLeaf : Highlighted → Bool
  | .token ⟨.keyword .., _⟩ => true
  | _ => false

private def isTokenLeaf (p : String → Bool) : Highlighted → Bool
  | .token ⟨_, content⟩ => p content.trimAscii.toString
  | _ => false

private partial def flattenHighlightedLeaves : Highlighted → Array Highlighted
  | .seq xs => xs.foldl (init := #[]) fun acc x => acc ++ flattenHighlightedLeaves x
  | .span _ content => flattenHighlightedLeaves content
  | .tactics _ _ _ content => flattenHighlightedLeaves content
  | leaf => #[leaf]

private def tokenText? : Highlighted → Option String
  | .token ⟨_, content⟩ => some content.trimAscii.toString
  | _ => none

private def isProjectionTarget? (leaf : Highlighted) : Bool :=
  match tokenText? leaf with
  | some "toReal" => true
  | some "run" => true
  | _ => false

private def isProjectionDotGlitch (text : String) : Bool :=
  text == "" || text == "f" || text == "e" || text == "l" || text == "/"

private def normalizeProjectionDots (leaves : Array Highlighted) : Array Highlighted :=
  leaves.mapIdx fun idx leaf =>
    match leaf with
    | .token ⟨kind, content⟩ =>
      let text := content.trimAscii.toString
      if isProjectionDotGlitch text && leaves[idx + 1]?.any isProjectionTarget? then
        .token ⟨kind, "."⟩
      else
        leaf
    | _ => leaf

private def firstIndex? (xs : Array α) (p : α → Bool) : Option Nat := Id.run do
  for i in [:xs.size] do
    match xs[i]? with
    | some x =>
      if p x then
        return some i
    | none => pure ()
  return none

private def lastIndex? (xs : Array α) (p : α → Bool) : Option Nat := Id.run do
  for i in [:xs.size] do
    let idx := xs.size - 1 - i
    match xs[idx]? with
    | some x =>
      if p x then
        return some idx
    | none => pure ()
  return none

private partial def prevKeywordIndex? (leaves : Array Highlighted) (idx : Nat) : Option Nat :=
  if idx == 0 then
    none
  else
    let idx := idx - 1
    match leaves[idx]? with
    | some leaf =>
      if isAnyKeywordLeaf leaf then some idx else prevKeywordIndex? leaves idx
    | none => none

private def isDeclPrimaryKeyword (s : String) : Bool :=
  #["def", "abbrev", "structure", "inductive", "theorem", "lemma"].contains s

private def isDeclModifierKeyword (s : String) : Bool :=
  #["private", "noncomputable"].contains s

private partial def rewindDeclModifiers (leaves : Array Highlighted) (idx : Nat) : Nat :=
  match prevKeywordIndex? leaves idx with
  | some prev =>
    match leaves[prev]? with
    | some leaf =>
      if isKeywordLeaf isDeclModifierKeyword leaf then
        rewindDeclModifiers leaves prev
      else
        idx
    | none => idx
  | none => idx

private def trimHighlightedWrapper (highlighted : Highlighted) : Highlighted :=
  let leaves := flattenHighlightedLeaves highlighted
  let start := (firstIndex? leaves (isKeywordLeaf isSourceStartKeyword)).getD 0
  let leaves := leaves.extract start leaves.size
  let stop := (lastIndex? leaves (isKeywordLeaf (· == "end"))).getD leaves.size
  .seq (normalizeProjectionDots (leaves.extract 0 stop))

private def trimStatementHighlightedWrapper (highlighted : Highlighted) : Highlighted :=
  let leaves := flattenHighlightedLeaves highlighted
  let start := (firstIndex? leaves (isKeywordLeaf isSourceStartKeyword)).getD 0
  let leaves := leaves.extract start leaves.size
  let stop := (firstIndex? leaves (isTokenLeaf (· == ":="))).getD leaves.size
  .seq (normalizeProjectionDots (leaves.extract 0 stop))

block_extension Block.leanSource (declName : String) (source : String) where
  data := toJson (declName, source)
  traverse _id _data _contents := do
    pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        pure <| .raw ("\\paragraph{Lean source: " ++ declName ++ "}\\begin{verbatim}\n" ++
          source ++ "\n\\end{verbatim}\n")
      | .error _ => pure .empty
  toHtml :=
    some <| fun _goI goB _id data contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        let rendered ← contents.mapM goB
        let title := s!"Lean source: {declName}"
        let body :=
          if contents.isEmpty then
            Verso.Output.Html.tag "pre" #[
              ("class", "sm-lean-source-code")
            ] (Verso.Output.Html.text true source)
          else
            Verso.Output.Html.tag "div" #[
              ("class", "sm-lean-source-rendered")
            ] (.seq rendered)
        pure <|
          Verso.Output.Html.tag "section" #[
            ("class", "sm-lean-source")
          ] <| .seq #[
            Verso.Output.Html.tag "div" #[
              ("class", "sm-lean-source-summary")
            ] (Verso.Output.Html.text true title),
            body
          ]
      | .error _ => pure .empty

block_extension Block.leanStatement (declName : String) (source : String) where
  data := toJson (declName, source)
  traverse _id _data _contents := do
    pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        pure <| .raw ("\\paragraph{Lean statement: " ++ declName ++ "}\\begin{verbatim}\n" ++
          source ++ "\n\\end{verbatim}\n")
      | .error _ => pure .empty
  toHtml :=
    some <| fun _goI goB _id data contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        let rendered ← contents.mapM goB
        let title := s!"Lean statement: {declName}"
        let body :=
          if contents.isEmpty then
            Verso.Output.Html.tag "pre" #[
              ("class", "sm-lean-source-code")
            ] (Verso.Output.Html.text true source)
          else
            Verso.Output.Html.tag "div" #[
              ("class", "sm-lean-source-rendered")
            ] (.seq rendered)
        pure <|
          Verso.Output.Html.tag "section" #[
            ("class", "sm-lean-source sm-lean-statement")
          ] <| .seq #[
            Verso.Output.Html.tag "div" #[
              ("class", "sm-lean-source-summary")
            ] (Verso.Output.Html.text true title),
            body
          ]
      | .error _ => pure .empty

private meta def sourcePreviewTerm? (declName moduleName : Name) (source : String) :
    DocElabM (Option Term) := do
  if isPreviewableSource source then
    let pre := previewPrefix moduleName declName
    let post := previewSuffix declName
    let wrapped : StrLit := Syntax.mkStrLit (pre ++ source ++ post)
    let cfg : Verso.Genre.Manual.InlineLean.LeanBlockConfig := {
      «show» := true
      keep := false
      name := none
      error := false
      fresh := false
    }
    try
      let term ←
        Verso.Genre.Manual.InlineLean.elabCommands cfg wrapped
          (fun _shouldShow highlighted _str => do
            let highlighted := trimHighlightedWrapper highlighted
            ``(Block.other (_root_.Block.leanSource $(quote declName.toString) $(quote source)) #[
                Block.other
                  (Verso.Genre.Manual.InlineLean.Block.lean
                    $(quote highlighted)
                    (none : Option System.FilePath)
                    (none : Option Lean.Lsp.Range))
                  #[]
              ]))
      pure (some term)
    catch
      | _ => pure none
  else
    pure none

private meta def statementPreviewTerm? (declName moduleName : Name) (statement : String) :
    DocElabM (Option Term) := do
  let pre := theoremPreviewPrefix moduleName declName
  let post := previewSuffix declName
  let wrapped : StrLit := Syntax.mkStrLit (pre ++ statement ++ " := smDocsProof" ++ post)
  let cfg : Verso.Genre.Manual.InlineLean.LeanBlockConfig := {
    «show» := true
    keep := false
    name := none
    error := false
    fresh := false
  }
  try
    let term ←
      Verso.Genre.Manual.InlineLean.elabCommands cfg wrapped
        (fun _shouldShow highlighted _str => do
          let highlighted := trimStatementHighlightedWrapper highlighted
          ``(Block.other (_root_.Block.leanStatement $(quote declName.toString) $(quote statement)) #[
              Block.other
                (Verso.Genre.Manual.InlineLean.Block.lean
                  $(quote highlighted)
                  (none : Option System.FilePath)
                  (none : Option Lean.Lsp.Range))
                #[]
            ]))
    pure (some term)
  catch
    | _ => pure none

private meta def sourceBlockTerm (cfg : SourceConfig) : DocElabM Term := do
  let declName := cfg.name.getId
  let extracted ← extractDeclBody declName
  if isTheoremLikeSource extracted.source then
    let statement := (theoremStatementSource? extracted.source).getD extracted.source
    let preview? ← statementPreviewTerm? declName extracted.moduleName statement
    match preview? with
    | some term => pure term
    | none =>
      ``(Block.other (Block.leanStatement $(quote declName.toString) $(quote statement)) #[])
  else
    let preview? ← sourcePreviewTerm? declName extracted.moduleName extracted.source
    match preview? with
    | some term => pure term
    | none =>
      ``(Block.other (Block.leanSource $(quote declName.toString) $(quote extracted.source)) #[])

/--
Extracts a live Lean declaration and renders it as a local source panel.
Definitions render as source. Theorems and lemmas render as interactive
statements only; readers can open the Lean file for proof terms.
-/
@[code_block]
meta def leanSource : SourceConfig → StrLit → DocElabM Term
  | cfg, _code => sourceBlockTerm cfg

/--
Elaborates a small Lean command block using Verso's Lean highlighter under a
local, unambiguous code-block name. This avoids the `lean` name clash between
Verso Manual and Verso Blueprint's informal genre.
-/
@[code_block]
meta def liveLean :
    Verso.Genre.Manual.InlineLean.LeanBlockConfig → StrLit → DocElabM Term
  | cfg, code =>
      Verso.Genre.Manual.InlineLean.elabCommands cfg code
        (fun shouldShow highlighted _str => do
          if !shouldShow then
            ``(Block.concat #[])
          else
            ``(Block.other
                (Verso.Genre.Manual.InlineLean.Block.lean
                  $(quote highlighted)
                  (none : Option System.FilePath)
                  (none : Option Lean.Lsp.Range))
                #[]))
