import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Chapters.AEAD.Defs
import SecureMessagingDocs.Chapters.AEAD.AESGCM
import SecureMessagingDocs.Chapters.AEAD.EncryptThenMAC

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "Authenticated Encryption with Associated Data" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.AEAD.Defs}

{include 1 SecureMessagingDocs.Chapters.AEAD.AESGCM}

{include 1 SecureMessagingDocs.Chapters.AEAD.EncryptThenMAC}
