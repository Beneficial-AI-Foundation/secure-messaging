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
import SMDocs.CkaDiagrams

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

A proof-of-concept for documenting the `SecureMessaging` Lean formalization with
*Verso-Blueprint*: paper-quality mathematical documents whose every claim is backed by
live, machine-checked Lean code that cannot silently drift out of sync with the library.

*What this shows* — each Verso-Blueprint capability is demonstrated by one self-contained
example page; follow a link to open it:

- *Custom TeX / KaTeX notation* — {ref "tex_notation"}[Custom TeX and KaTeX Notation].
  Define cryptographic macros (sampling and labelled protocol-message arrows, encryption
  and decryption operators, …) once in a shared module and reuse them in every formula
  across the site; edit a macro in one place and every use updates.
- *Formal claims backed by live Lean, hover types, and citations* —
  {ref "cka_from_ddh"}[CKA from Diffie-Hellman]. Paper-style definitions and theorems are
  paired with the real declarations that realise them (`CKAScheme`, `ddhCKA`,
  `ddhCKA.correctness`): hover any name to read its type off the live library, and renaming
  a referenced declaration *fails the build* rather than letting the prose drift. Includes
  an `@[bib]` bibliography with inline citations.
- *Cryptographic diagrams* — {ref "cka_diagrams"}[CKA Protocol Flow and Security Game].
  A two-party message-sequence chart and a security-game pseudocode block, built from KaTeX
  plus a small custom HTML `block_extension` — no external diagram tooling.
- *Dependency graph, status summary, and bibliography* — generated automatically from the
  `{uses …}` edges between nodes and the kernel-checked proof status of the linked
  declarations. See the *Dependency graph*, *Blueprint summary*, and *Bibliography* pages in
  the navigation sidebar.
- *Protocol progress chart* — _in progress_: a dashboard tracking how many protocols are
  specified and formally verified.

The example pages follow.

{include 1 SMDocs.TexStub}

{include 1 SMDocs.CkaFromDdh}

{include 1 SMDocs.CkaDiagrams}

{blueprint_graph}

{blueprint_summary}

{blueprint_bibliography}
