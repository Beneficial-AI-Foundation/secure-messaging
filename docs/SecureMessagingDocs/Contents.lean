import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Chapters.AEAD
import SecureMessagingDocs.Chapters.CKA
import SecureMessagingDocs.Chapters.CKAProtocols
import SecureMessagingDocs.Chapters.ErasureCodes
import SecureMessagingDocs.Chapters.FSAEAD
import SecureMessagingDocs.Chapters.OnOffKEM
import SecureMessagingDocs.Chapters.PRFPRNG
import SecureMessagingDocs.Chapters.RKEM
import SecureMessagingDocs.Chapters.SecureMessaging

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Informal

set_option doc.verso true

#doc (Manual) "Secure Messaging — Lean Formalization" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "Secure Messaging"
%%%

A Lean 4 formalization of secure messaging protocols,
building on the VCVio framework for verified cryptography.

The source code is available on
[GitHub](https://github.com/Beneficial-AI-Foundation/secure-messaging/).

# Overview

The goal of this project is to provide machine-checked proofs of correctness
and security properties for cryptographic messaging protocols.

{blueprint_graph}

{blueprint_summary}

{include 0 SecureMessagingDocs.Chapters.AEAD}

{include 0 SecureMessagingDocs.Chapters.CKA}

{include 0 SecureMessagingDocs.Chapters.CKAProtocols}

{include 0 SecureMessagingDocs.Chapters.ErasureCodes}

{include 0 SecureMessagingDocs.Chapters.FSAEAD}

{include 0 SecureMessagingDocs.Chapters.OnOffKEM}

{include 0 SecureMessagingDocs.Chapters.PRFPRNG}

{include 0 SecureMessagingDocs.Chapters.RKEM}

{include 0 SecureMessagingDocs.Chapters.SecureMessaging}

{blueprint_bibliography}

