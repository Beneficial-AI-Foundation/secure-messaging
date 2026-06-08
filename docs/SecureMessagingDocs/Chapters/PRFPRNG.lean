import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.PRFPRNG.Defs
import SecureMessagingDocs.Chapters.PRFPRNG.FromPRPPRG

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "PRF-PRNG" =>

*References:*

- {Informal.citet ACD19}[]

{include 1 SecureMessagingDocs.Chapters.PRFPRNG.Defs}

{include 1 SecureMessagingDocs.Chapters.PRFPRNG.FromPRPPRG}
