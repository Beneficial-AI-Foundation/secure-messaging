/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import SMDocs.Contents

/-!
# Site generator

Renders the Verso-Blueprint site to static HTML. From the repository root:

    lake -d docs build SMDocs
    lake -d docs env lean --run docs/Main.lean --output docs/_out/site

The site lands in `docs/_out/site/html-multi/`.
-/

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc SMDocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
