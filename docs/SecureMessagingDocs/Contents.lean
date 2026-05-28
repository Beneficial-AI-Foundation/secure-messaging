/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

import SecureMessagingDocs.SourceBlock
import SecureMessagingDocs.BlueprintTriptych
import SecureMessagingDocs.Prerequisites

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

`SecureMessaging` is a Lean 4 library of common cryptographic building blocks
used across two-party secure-messaging stacks. It is intended to be consumed by
later formalization projects — primarily a future Lean formalization of
[libsignal](https://github.com/signalapp/libsignal), Signal's secure-messaging
stack. libsignal historically centers on the Double Ratchet and now also ships
post-quantum components alongside it; *SPQR*, the post-quantum two-party
secure messaging algorithm of Auerbach–Dodis–Jost–Katsumata–Schmidt (USENIX
'25), is one such PQ algorithm inside libsignal and is built on the Triple
Ratchet.

This documentation site is the companion to that library. It connects each
Lean definition to the cryptographic paper it implements, the polynomial /
free-monad / probability scaffolding it sits on, and the game-based security
statement it ultimately formalizes.

:::group "secure_messaging_docs"
Documentation for the `SecureMessaging` Lean formalization and its
VCV-io-based game definitions.
:::

# Scope
%%%
number := false
%%%

The current scope covers:

- *CKA* — Continuous Key Agreement, the asymmetric two-party building block
  underlying the Double Ratchet (Alwen–Coretti–Dodis).
- *CKA from KEM* — generic compilation of a CKA scheme from a KEM, used in
  hybrid-secure protocols.
- *AEAD / AEDE* — authenticated encryption with associated data, including
  the AEDE notion used by the Triple Ratchet (Dodis–Jost–Katsumata–Prest–
  Schmidt).

Planned future chapters (tracked in the repository's issues) include the
double and triple ratchet themselves, and concrete post-quantum primitives
such as ML-KEM. Each of these will be added as its own chapter so that
downstream projects can cite a single named correctness or security theorem
in this library.

# How To Read This Site
%%%
number := false
%%%

The site is organized so every protocol chapter reads from three directions:

* from the cryptographic papers, by identifying which paper object each Lean
  definition models;
* from the mathematics, by making the relevant state spaces, maps, polynomial
  signatures, and free-monad structure explicit;
* from the Lean code, by pointing to the structures, games, adversary types,
  and theorem statements that implement the paper model.

The basic reading map shared across chapters is:

```
paper algorithm       <-> Lean construction definition
paper game oracle     <-> OracleSpec query shape plus QueryImpl semantics
adversary             <-> OracleComp program over the oracle polynomial
security claim        <-> theorem statement over game advantages
game hop/reduction    <-> proof between theorem statements
```

Before reading any protocol chapter, read Section 0 below. It records the
shared VCV-io oracle-game encoding (polynomial functors, free monads,
`QueryImpl`, `simulateQ`, `ProbComp`, `evalDist`) that every chapter in this
library reuses without restating.

{include 1 SecureMessagingDocs.Prerequisites}
