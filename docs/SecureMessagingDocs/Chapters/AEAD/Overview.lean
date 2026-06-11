import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.AEAD.Defs
import SecureMessagingDocs.Chapters.AEAD.AESGCM
import SecureMessagingDocs.Chapters.AEAD.EncryptThenMAC

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "Authenticated Encryption with Associated Data" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]
- {Informal.citet BN00}[]
- {Informal.citet Rog02}[]
- {Informal.citet NIST_GCM}[]

{include 1 SecureMessagingDocs.Chapters.AEAD.Defs}

{include 1 SecureMessagingDocs.Chapters.AEAD.AESGCM}

{include 1 SecureMessagingDocs.Chapters.AEAD.EncryptThenMAC}

{blueprint_graph}

{blueprint_summary}
