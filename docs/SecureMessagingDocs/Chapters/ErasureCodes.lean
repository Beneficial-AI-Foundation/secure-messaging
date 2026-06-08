import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.ErasureCodes.Defs
import SecureMessagingDocs.Chapters.ErasureCodes.ReedSolomon

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Erasure Codes" =>

*References:*

- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.ErasureCodes.Defs}

{include 1 SecureMessagingDocs.Chapters.ErasureCodes.ReedSolomon}
