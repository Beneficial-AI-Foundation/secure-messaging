import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.OnOffKEM.Defs
import SecureMessagingDocs.Chapters.OnOffKEM.FromMLKEM

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Online-Offline KEM" =>

*References:*

- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.OnOffKEM.Defs}

{include 1 SecureMessagingDocs.Chapters.OnOffKEM.FromMLKEM}

{blueprint_graph}

{blueprint_summary}
