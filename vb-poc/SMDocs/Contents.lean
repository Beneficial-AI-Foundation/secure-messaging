/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SMDocs.TexStub
import SMDocs.CkaFromDdh

/-!
# Blueprint root

Verso-Blueprint landing page for the `SecureMessaging` formalization. It wires the
capability stubs into one site and renders the dependency graph, status summary,
and bibliography. Each stub is a single minimal page.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "SecureMessaging — Verso-Blueprint PoC" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "SM VB PoC"
%%%

A minimal Verso-Blueprint documentation scaffold for the `SecureMessaging` Lean
formalization. This page establishes the build-and-deploy pipeline; the
documentation content arrives in later phases.

:::definition "poc_scaffold"
Placeholder blueprint node, so the dependency graph and the status summary have
something to render while the scaffold is verified end to end.
:::

Capability stubs, one page each:

{include 1 SMDocs.TexStub}

{include 1 SMDocs.CkaFromDdh}

{blueprint_graph}

{blueprint_summary}

{blueprint_bibliography}
