import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.SCKA.Defs
import SecureMessagingDocs.Chapters.SCKA.MLKEMBraid
import SecureMessagingDocs.Chapters.SCKA.SPQR
import SecureMessagingDocs.Chapters.SCKA.OppUniKEM
import SecureMessagingDocs.Chapters.SCKA.OppBiKEM
import SecureMessagingDocs.Chapters.SCKA.OppRKEM

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option linter.hashCommand false

#doc (Manual) "Sparse Continuous Key Agreement" =>

*References:*

- {Informal.citet SCKA25}[]
- {Informal.citet MLKEM_Braid}[]
- {Informal.citet SPQR}[]

{include 1 SecureMessagingDocs.Chapters.SCKA.Defs}

{include 1 SecureMessagingDocs.Chapters.SCKA.MLKEMBraid}

{include 1 SecureMessagingDocs.Chapters.SCKA.SPQR}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppUniKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppBiKEM}

{include 1 SecureMessagingDocs.Chapters.SCKA.OppRKEM}

{blueprint_graph}

{blueprint_summary}
