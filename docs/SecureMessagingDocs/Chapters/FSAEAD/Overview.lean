import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.FSAEAD.Defs
import SecureMessagingDocs.Chapters.FSAEAD.FromAEADPRG

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Forward-Secure AEAD" =>

*References:*

- {Informal.citet ACD19}[]

{include 1 SecureMessagingDocs.Chapters.FSAEAD.Defs}

{include 1 SecureMessagingDocs.Chapters.FSAEAD.FromAEADPRG}

{blueprint_graph}

{blueprint_summary}
