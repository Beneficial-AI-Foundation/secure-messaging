/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary

/-!
# Blueprint root

Minimal Verso-Blueprint landing page for the `SecureMessaging` formalization. It
exists only to prove the site builds, renders, and deploys. The four capability
stubs (TeX, Lean+LSP, diagrams, blueprint features) and the protocol progress
chart are added in later phases.
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

{blueprint_graph}

{blueprint_summary}
