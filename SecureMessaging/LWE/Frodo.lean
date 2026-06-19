/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.ProbComp

/-!
# Frodo/LWE CKA parameters

This file is the abstract interface used for the optimized Frodo/LWE CKA from
ACD19, Section 4.1.2. It is deliberately not the matrix implementation. The
record below names just the pieces of the protocol that the generic CKA
construction and correctness proof need: two send algorithms, two receive
algorithms, two "public key matches secret" relations, and the laws saying that
matched states really agree after a send/receive step.

The Frodo matrix work enters later through an instance of this record. In that
instance the common value is the public matrix `A`, public keys have the shape
`B = A * S + E` (or the opposite-direction analogue), and receive uses
reconciliation to turn approximate agreement into an exact key. At this level we
only remember that structure as `MatchAB`, `MatchBA`, and support-level
correctness laws for `sendA` and `sendB`.

## Party convention

The paper writes this CKA with B sending first. The CKA games in this repository
are A-first, so the names in this file follow the repository convention rather
than the paper's order. With that renaming, `sendA` is the paper's `CKA-S-B`,
`recvB` is `CKA-R-A`, `sendB` is `CKA-S-A`, and `recvA` is `CKA-R-B`.

## Shape of one round

Think of `Common` as the fixed public value shared by both sides. Initially A
has a public key `PubAB`, B has the matching secret `SecAB`, and `MatchAB`
records that they are paired. An A-to-B step runs `sendA`: it outputs an epoch
key, sends a fresh public key `PubBA` together with a reconciliation `Hint`, and
keeps the next secret `SecBA`. Then `recvB`, using `SecAB` and the transmitted
`(PubBA, Hint)`, must recover the same epoch key. The B-to-A step is the same
story with the two directions swapped; its pairing relation is `MatchBA`.
-/

open OracleSpec OracleComp

universe u

namespace Frodo

/-- Algorithms and reconciliation facts of the optimized Frodo/LWE CKA.

The type fields name the value spaces of the protocol; the data fields are the
side-specific send and receive algorithms; the relation fields `MatchAB` and
`MatchBA` describe when a public key and a secret are paired for the two key
directions; and the proposition fields are the support-level laws that a concrete
Frodo instance must satisfy. The monad `m` carries the sampling done by the send
algorithms, instantiated by `ProbComp` for the protocol construction.
-/
structure CKAParams (m : Type → Type u) [Monad m] [HasEvalSet m] where
  /-- The fixed public value shared by both parties, e.g. the Frodo public matrix. -/
  Common : Type
  /-- Public key held by A before a send, matched by `SecAB`. -/
  PubAB : Type
  /-- Public key produced by A's send and consumed by B's send, matched by `SecBA`. -/
  PubBA : Type
  /-- Secret held by B that pairs with a `PubAB`. -/
  SecAB : Type
  /-- Secret held by A that pairs with a `PubBA`. -/
  SecBA : Type
  /-- Epoch key derived in each round. -/
  Key : Type
  /-- Reconciliation hint transmitted alongside a public key. -/
  Hint : Type
  /-- Randomness sampled by A's send. -/
  RandA : Type
  /-- Randomness sampled by B's send. -/
  RandB : Type
  /-- Initial setup: the common value, A's first public key, and B's first secret. -/
  init : m (Common × PubAB × SecAB)
  /-- A's send (paper `CKA-S-B`): from the common value and A's public key, derive
  an epoch key, a fresh public key, a hint, A's next secret, and the randomness used. -/
  sendA : Common → PubAB → m (Key × PubBA × Hint × SecBA × RandA)
  /-- B's send (paper `CKA-S-A`): from the common value and B's public key, derive
  an epoch key, a fresh public key, a hint, B's next secret, and the randomness used. -/
  sendB : Common → PubBA → m (Key × PubAB × Hint × SecAB × RandB)
  /-- B's receive: recover the epoch key from B's secret and the
  public key and hint sent by A. -/
  recvB : Common → SecAB → PubBA → Hint → Option Key
  /-- A's receive: recover the epoch key from A's secret and the
  public key and hint sent by B. -/
  recvA : Common → SecBA → PubAB → Hint → Option Key
  /-- A public key and a secret are paired for the A-to-B direction. -/
  MatchAB : Common → PubAB → SecAB → Prop
  /-- A public key and a secret are paired for the B-to-A direction. -/
  MatchBA : Common → PubBA → SecBA → Prop
  /-- Setup produces a paired public key and secret. -/
  init_match : ∀ common pubAB secAB,
    (common, pubAB, secAB) ∈ support init → MatchAB common pubAB secAB
  /-- When A's public key and B's secret are paired, B's receive recovers exactly
  the epoch key produced by A's send. -/
  sendA_correct : ∀ common pubAB secAB, MatchAB common pubAB secAB →
    ∀ key pubBA hint secBA randA,
      (key, pubBA, hint, secBA, randA) ∈ support (sendA common pubAB) →
      recvB common secAB pubBA hint = some key
  /-- A's send produces a public key and a secret paired for the next direction. -/
  sendA_match_next : ∀ common pubAB key pubBA hint secBA randA,
      (key, pubBA, hint, secBA, randA) ∈ support (sendA common pubAB) →
      MatchBA common pubBA secBA
  /-- When B's public key and A's secret are paired, A's receive recovers exactly
  the epoch key produced by B's send. -/
  sendB_correct : ∀ common pubBA secBA, MatchBA common pubBA secBA →
    ∀ key pubAB hint secAB randB,
      (key, pubAB, hint, secAB, randB) ∈ support (sendB common pubBA) →
      recvA common secBA pubAB hint = some key
  /-- B's send produces a public key and a secret paired for the next direction. -/
  sendB_match_next : ∀ common pubBA key pubAB hint secAB randB,
      (key, pubAB, hint, secAB, randB) ∈ support (sendB common pubBA) →
      MatchAB common pubAB secAB

end Frodo
