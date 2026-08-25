/-
Unified Verso manual: every chapter in one `#doc`. CI and
`scripts/render-docs-site.sh` render this, then overlay the project landing page.
-/
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.AEAD.Overview
import SecureMessagingDocs.Chapters.CKA.Overview
import SecureMessagingDocs.Chapters.ErasureCodes.Overview
import SecureMessagingDocs.Chapters.FSAEAD.Overview
import SecureMessagingDocs.Chapters.KEM.Overview
import SecureMessagingDocs.Chapters.PRFPRNG.Overview
import SecureMessagingDocs.Chapters.RKEM.Overview
import SecureMessagingDocs.Chapters.SCKA.Overview
import SecureMessagingDocs.Chapters.SecureMessaging.Overview

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
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

{include 0 SecureMessagingDocs.Chapters.AEAD.Overview}

{include 0 SecureMessagingDocs.Chapters.CKA.Overview}

{include 0 SecureMessagingDocs.Chapters.ErasureCodes.Overview}

{include 0 SecureMessagingDocs.Chapters.FSAEAD.Overview}

{include 0 SecureMessagingDocs.Chapters.KEM.Overview}

{include 0 SecureMessagingDocs.Chapters.PRFPRNG.Overview}

{include 0 SecureMessagingDocs.Chapters.RKEM.Overview}

{include 0 SecureMessagingDocs.Chapters.SCKA.Overview}

{include 0 SecureMessagingDocs.Chapters.SecureMessaging.Overview}

{blueprint_bibliography}
