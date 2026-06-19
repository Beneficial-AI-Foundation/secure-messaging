/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.Defs
import SecureMessaging.LWE.Frodo
import SecureMessaging.LWE.Frodo.Matrix

/-!
# Continuous Key Agreement from the Frodo/LWE Construction

This file instantiates the abstract `CKAScheme` interface with the optimized
Frodo/LWE continuous key agreement of [ACD19, Section 4.1.2], packaged as a
`Frodo.CKAParams`. Here [ACD19] denotes Alwen, Coretti, and Dodis, *The Double
Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol*.

The paper presents the Frodo/LWE CKA with B sending first; the repository's CKA
game is A-first. The construction therefore follows the paper up to the
party-label swap recorded in `Frodo.CKAParams`: A runs the algorithms the paper
gives to B and vice versa, so the protocol is the paper's up to renaming of
parties.

## States and messages

A party's local state records both its role (sender or receiver) and the key
material it currently holds:

* `sendAReady common pubAB` — A is about to send and holds its public key;
* `recvAReady common secBA` — A is about to receive and holds the secret matching
  the public key it last sent;
* `sendBReady common pubBA` — B is about to send and holds the public key it last
  received;
* `recvBReady common secAB` — B is about to receive and holds its secret.

A message is a fresh public key together with a reconciliation hint, tagged by
its direction: `fromA` for an A-to-B message and `fromB` for a B-to-A message.
The initial shared key material is the common value with A's first public key and
B's first secret, and the send randomness is the randomness of whichever party
sent, tagged by `Sum`.
-/

open OracleSpec OracleComp

namespace lweCKA

/-- Phase- and direction-tagged CKA state for the Frodo/LWE construction.

Each constructor records the party, whether its next local action is a send or a
receive, and the key material it holds at that point. -/
inductive State (p : Frodo.CKAParams ProbComp) where
  /-- A is ready to send and holds its current public key. -/
  | sendAReady : p.Common → p.PubAB → State p
  /-- A is ready to receive and holds the secret matching the key it last sent. -/
  | recvAReady : p.Common → p.SecBA → State p
  /-- B is ready to send and holds the public key it last received. -/
  | sendBReady : p.Common → p.PubBA → State p
  /-- B is ready to receive and holds its current secret. -/
  | recvBReady : p.Common → p.SecAB → State p

/-- CKA messages produced by the Frodo/LWE construction.

A message carries a fresh public key and a reconciliation hint. The tag records
its direction so the receiver can reject a message sent in the wrong orientation. -/
inductive Message (p : Frodo.CKAParams ProbComp) where
  /-- Message from A to B: a `PubBA` public key and a hint. -/
  | fromA : p.PubBA → p.Hint → Message p
  /-- Message from B to A: a `PubAB` public key and a hint. -/
  | fromB : p.PubAB → p.Hint → Message p

/-- Initial shared key material: the common value, A's first public key, and B's
first secret. -/
abbrev InitKey (p : Frodo.CKAParams ProbComp) := p.Common × p.PubAB × p.SecAB

/-- Send randomness: A's randomness on the left, B's on the right. -/
abbrev Rand (p : Frodo.CKAParams ProbComp) := Sum p.RandA p.RandB

/-- Initialize the party that sends first with the common value and its public key. -/
def initA (p : Frodo.CKAParams ProbComp) (ik : InitKey p) : State p :=
  .sendAReady ik.1 ik.2.1

/-- Initialize the party that receives first with the common value and its secret. -/
def initB (p : Frodo.CKAParams ProbComp) (ik : InitKey p) : State p :=
  .recvBReady ik.1 ik.2.2

/-- A's send.

From `sendAReady common pubAB`, run the Frodo send to obtain the epoch key, a
fresh public key `pubBA`, a hint, and the secret `secBA` kept for the next
receive. Emit `fromA pubBA hint` and move to `recvAReady common secBA`. Called
outside the send phase, the algorithm returns `none`. -/
def sendA (p : Frodo.CKAParams ProbComp) :
    State p → ProbComp (Option (p.Key × Message p × State p))
  | .sendAReady common pubAB => do
      let (key, pubBA, hint, secBA, _randA) ← p.sendA common pubAB
      return some (key, Message.fromA pubBA hint, State.recvAReady common secBA)
  | _ => return none

/-- Randomness-leaking version of A's send.

Same transition as `sendA`, but the output also records A's send randomness,
tagged with `Sum.inl`. -/
def sendA_rleak (p : Frodo.CKAParams ProbComp) :
    State p → ProbComp (Option (p.Key × Message p × State p × Rand p))
  | .sendAReady common pubAB => do
      let (key, pubBA, hint, secBA, randA) ← p.sendA common pubAB
      return some (key, Message.fromA pubBA hint, State.recvAReady common secBA, Sum.inl randA)
  | _ => return none

/-- A's receive.

From `recvAReady common secBA` and a `fromB pubAB hint` message, run the Frodo
receive to recover the epoch key, then move to `sendAReady common pubAB`, keeping
the public key just received. A wrong state or message orientation returns `none`,
as does a failed Frodo receive. -/
def recvA (p : Frodo.CKAParams ProbComp) :
    State p → Message p → Option (p.Key × State p)
  | .recvAReady common secBA, .fromB pubAB hint =>
      match p.recvA common secBA pubAB hint with
      | some key => some (key, State.sendAReady common pubAB)
      | none => none
  | _, _ => none

/-- B's send.

From `sendBReady common pubBA`, run the Frodo send to obtain the epoch key, a
fresh public key `pubAB`, a hint, and the secret `secAB` kept for the next
receive. Emit `fromB pubAB hint` and move to `recvBReady common secAB`. Called
outside the send phase, the algorithm returns `none`. -/
def sendB (p : Frodo.CKAParams ProbComp) :
    State p → ProbComp (Option (p.Key × Message p × State p))
  | .sendBReady common pubBA => do
      let (key, pubAB, hint, secAB, _randB) ← p.sendB common pubBA
      return some (key, Message.fromB pubAB hint, State.recvBReady common secAB)
  | _ => return none

/-- Randomness-leaking version of B's send.

Same transition as `sendB`, but the output also records B's send randomness,
tagged with `Sum.inr`. -/
def sendB_rleak (p : Frodo.CKAParams ProbComp) :
    State p → ProbComp (Option (p.Key × Message p × State p × Rand p))
  | .sendBReady common pubBA => do
      let (key, pubAB, hint, secAB, randB) ← p.sendB common pubBA
      return some (key, Message.fromB pubAB hint, State.recvBReady common secAB, Sum.inr randB)
  | _ => return none

/-- B's receive.

From `recvBReady common secAB` and a `fromA pubBA hint` message, run the Frodo
receive to recover the epoch key, then move to `sendBReady common pubBA`, keeping
the public key just received. A wrong state or message orientation returns `none`,
as does a failed Frodo receive. -/
def recvB (p : Frodo.CKAParams ProbComp) :
    State p → Message p → Option (p.Key × State p)
  | .recvBReady common secAB, .fromA pubBA hint =>
      match p.recvB common secAB pubBA hint with
      | some key => some (key, State.sendBReady common pubBA)
      | none => none
  | _, _ => none

/-- The Frodo/LWE CKA scheme.

The type parameters specialize the abstract CKA interface as follows:

* `IK = InitKey p`, the common value with A's first public key and B's first
  secret;
* `St = State p`, the phase- and direction-tagged local state;
* `I = p.Key`, the Frodo epoch key;
* `Rho = Message p`, the protocol-message space;
* `Rand = Rand p`, the per-send randomness of whichever party sent.

The send and receive algorithms are side-specific, following the paper's
optimized Frodo/LWE CKA up to the A-first party-label swap recorded in
`Frodo.CKAParams`. -/
-- ANCHOR: scheme
def scheme (p : Frodo.CKAParams ProbComp) :
    CKAScheme ProbComp (InitKey p) (State p) p.Key (Message p) (Rand p) where
  initKeyGen := p.init
  initA := fun ik => return initA p ik
  initB := fun ik => return initB p ik
  sendA := sendA p
  sendA_rleak := sendA_rleak p
  recvA := recvA p
  sendB := sendB p
  sendB_rleak := sendB_rleak p
  recvB := recvB p
-- ANCHOR_END: scheme

/-- The concrete Frodo/LWE CKA scheme over a `Frodo.MatrixParams`.

This specializes `scheme` to `Frodo.concreteCKAParams p`, the matrix model where
the public matrix `A`, the public key `B = A * S + E`, the fresh public keys
`B'`, the shared values `V'`, the reconciliation hint `hint`, and the
reconciliation map `reconcile` are concrete matrix expressions over `ZMod q`. -/
-- ANCHOR: frodoScheme
def frodoScheme (p : Frodo.MatrixParams) :
    CKAScheme ProbComp (InitKey (Frodo.concreteCKAParams p))
      (State (Frodo.concreteCKAParams p)) p.Key
      (Message (Frodo.concreteCKAParams p)) (Rand (Frodo.concreteCKAParams p)) :=
  scheme (Frodo.concreteCKAParams p)
-- ANCHOR_END: frodoScheme

end lweCKA
