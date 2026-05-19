/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

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
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "SecureMessaging Formalization Notes" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "SecureMessaging Docs"
%%%

This site documents the protocol specifications and supporting mathematical
interfaces used by the `SecureMessaging` formalization. It is a
VersoBlueprint companion for this repository, not a generated dependency report.

:::group "secure_messaging_docs"
Documentation for the `SecureMessaging` Lean formalization and its
VCV-io-based game definitions.
:::

The goal is to make the formalization readable from three directions:

* from the cryptographic papers, by identifying which paper object each Lean
  definition models;
* from the mathematics, by making the relevant state spaces, maps, polynomial
  signatures, and free-monad structure explicit;
* from the Lean code, by pointing to the structures, games, adversary types, and
  theorem statements that implement the paper model.

The basic reading map is:

```
paper algorithm       <-> Lean construction definition
paper game oracle     <-> OracleSpec query shape plus QueryImpl semantics
adversary             <-> OracleComp program over the oracle polynomial
security claim        <-> theorem statement over game advantages
game hop/reduction    <-> future proof between theorem statements
```

VCV-io is imported infrastructure. Its oracle machinery appears here only to
explain how `SecureMessaging` encodes cryptographic games: the protocol-specific
chapters remain about the protocols formalized in this repository.

The VCV-io chapter records the shared oracle-game encoding. The CKA-from-KEM
chapter records the Double Ratchet Section 4.1.2 construction, its paper-to-code
map, and the correctness/security property statements.

{include 1 SecureMessagingDocs.DocVCVioOracles}

{include 1 SecureMessagingDocs.DocCKAFromKEM}
