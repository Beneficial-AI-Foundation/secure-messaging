import SecureMessagingDocs.Render
import SecureMessagingDocs.Contents

/-!
Verso Blueprint generator entry point.

`lake exe vbp build` (the standard Verso Blueprint render command, and the
default used by tools such as `probe-leanblueprint`) discovers a generator by
looking for `BlueprintMain.lean` (among a few conventional names) at the
package root. This file is that entry point: it renders the unified manual
exactly like `docs/SecureMessagingDocs/Renderers/ContentsMain.lean` does,
through `SecureMessagingDocs.renderManual`, which wraps
`PreviewManifest.blueprintMainWithPreviewData`.

`scripts/render-docs-site.sh` remains the full site build (landing page,
Blueprint status table, progress chart); this entry point only produces the
manual and its `blueprint-manifest.json` under `_out/site`.
-/

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Contents) args
