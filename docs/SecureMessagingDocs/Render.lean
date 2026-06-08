import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Style

open Verso.Genre Manual
open Informal

namespace SecureMessagingDocs

private partial def outputDir? : List String → Option System.FilePath
  | "--output" :: path :: _ => some path
  | _ :: rest => outputDir? rest
  | [] => none

/-- Verso writes hover docs once to `-verso-docs.json` at the multi-page root;
copy it into every chapter/subsection directory so hover popups work everywhere. -/
private partial def copyHoverDocsToSubdirs (root : System.FilePath) : IO Unit := do
  let docsPath := root / "-verso-docs.json"
  unless ← docsPath.pathExists do
    return ()
  let docs ← IO.FS.readFile docsPath
  let rec visit (dir : System.FilePath) : IO Unit := do
    for entry in ← dir.readDir do
      if ← entry.path.isDir then
        IO.FS.writeFile (entry.path / "-verso-docs.json") docs
        visit entry.path
  visit root

def renderManual (manual : Verso.Doc.Part Manual) (args : List String) : IO UInt32 := do
  let exitCode ← PreviewManifest.manualMainWithSharedPreviewManifest
    manual
    args
    (extensionImpls := by exact extension_impls%)
    (config := docsConfig)
  if exitCode == 0 then
    if let some out := outputDir? args then
      copyHoverDocsToSubdirs (out / "html-multi")
  pure exitCode

end SecureMessagingDocs
