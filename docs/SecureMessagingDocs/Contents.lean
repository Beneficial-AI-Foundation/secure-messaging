/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary

import SecureMessagingDocs.SourceBlock
import SecureMessagingDocs.BlueprintTriptych
import SecureMessagingDocs.Cryptocode
import SecureMessagingDocs.DocVCVioOracles
import SecureMessagingDocs.DocCKAFromKEM

/-!
# SecureMessaging Docs Contents

Blueprint root for the SecureMessaging documentation.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Game-Based Security Proofs in VCV-io" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "SecureMessaging Docs"
%%%

This site documents the mathematical and code-level foundations used by the
`SecureMessaging` formalization: how polynomial functors, free monads, and
probabilistic monads in VCV-io combine into a reusable scaffold for
game-based security proofs.

Per-protocol chapters are added next to each formalization as it lands; this
chapter only describes the shared core.

{include 1 SecureMessagingDocs.DocVCVioOracles}

{include 1 SecureMessagingDocs.DocCKAFromKEM}

{blueprint_graph}

{blueprint_summary}
