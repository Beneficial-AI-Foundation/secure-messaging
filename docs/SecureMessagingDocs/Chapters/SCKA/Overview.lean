import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.SCKA.Defs
import SecureMessagingDocs.Chapters.SCKA.UniKEM
import SecureMessagingDocs.Chapters.SCKA.BiKEM
import SecureMessagingDocs.Chapters.SCKA.RKEM
import SecureMessagingDocs.Chapters.SCKA.OppUniKEM
import SecureMessagingDocs.Chapters.SCKA.OppBiKEM
import SecureMessagingDocs.Chapters.SCKA.OppRKEM

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Sparse Continuous Key Agreement" =>

*References:*

- {Informal.citet SCKA25}[]

{include 1 SecureMessagingDocs.Chapters.SCKA.Defs}

{include 1 SecureMessagingDocs.Chapters.SCKA.UniKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.BiKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.RKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppUniKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppBiKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppRKEM}

{blueprint_graph}

{blueprint_summary}
