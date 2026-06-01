import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Contents

open Verso.Genre Manual
open Informal

def main (args : List String) : IO UInt32 :=
  PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc SecureMessagingDocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := {})
