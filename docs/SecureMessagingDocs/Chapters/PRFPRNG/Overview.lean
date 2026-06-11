import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
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

{blueprint_graph}

{blueprint_summary}
