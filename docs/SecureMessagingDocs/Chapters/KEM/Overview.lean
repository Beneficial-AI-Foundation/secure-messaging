import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.KEM.MLKEM
import SecureMessagingDocs.Chapters.KEM.OnOffKEM.Overview

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Key Encapsulation Mechanism" =>

*References:*

- {Informal.citet SCKA25}[]
- {Informal.citet FIPS203}[]

{include 1 SecureMessagingDocs.Chapters.KEM.MLKEM}

{include 1 SecureMessagingDocs.Chapters.KEM.OnOffKEM.Overview}

{blueprint_graph}

{blueprint_summary}
