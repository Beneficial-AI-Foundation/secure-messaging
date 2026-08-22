import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.KEM.MLKEM
import SecureMessagingDocs.Chapters.KEM.FrodoKEM
import SecureMessagingDocs.Chapters.KEM.OnOffKEM.Overview
import SecureMessagingDocs.Chapters.KEM.IncrementalKEM.Overview

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option linter.hashCommand false

#doc (Manual) "Key Encapsulation Mechanism" =>

*References:*

- {Informal.citet SCKA25}[]
- {Informal.citet FIPS203}[]
- {Informal.citet FrodoKEM}[]
- {Informal.citet MLKEM_Braid}[]

{include 1 SecureMessagingDocs.Chapters.KEM.MLKEM}

{include 1 SecureMessagingDocs.Chapters.KEM.FrodoKEM}

{include 1 SecureMessagingDocs.Chapters.KEM.OnOffKEM.Overview}

{include 1 SecureMessagingDocs.Chapters.KEM.IncrementalKEM.Overview}

{blueprint_graph}

{blueprint_summary}
