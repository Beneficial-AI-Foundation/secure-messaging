import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.RKEM.Defs
import SecureMessagingDocs.Chapters.RKEM.FromDDHNonFS
import SecureMessagingDocs.Chapters.RKEM.FromDDHFS
import SecureMessagingDocs.Chapters.RKEM.FromKEM
import SecureMessagingDocs.Chapters.RKEM.KatanaPlain
import SecureMessagingDocs.Chapters.RKEM.KatanaOptimised

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Ratcheting KEM" =>

*References:*

- {Informal.citet TR25}[]

{include 1 SecureMessagingDocs.Chapters.RKEM.Defs}

{include 1 SecureMessagingDocs.Chapters.RKEM.FromDDHNonFS}

{include 1 SecureMessagingDocs.Chapters.RKEM.FromDDHFS}

{include 1 SecureMessagingDocs.Chapters.RKEM.FromKEM}

{include 1 SecureMessagingDocs.Chapters.RKEM.KatanaPlain}

{include 1 SecureMessagingDocs.Chapters.RKEM.KatanaOptimised}

{blueprint_graph}

{blueprint_summary}
