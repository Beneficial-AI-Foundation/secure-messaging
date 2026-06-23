/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.Defs
import SecureMessaging.CKA.FromLWE.Basic

/-!
# Continuous Key Agreement from the Frodo/LWE Construction

This file builds the concrete CKA scheme `lweCKA.frodoScheme` from a
`Frodo.MatrixParams` (the matrix model over `ZMod q` in
`SecureMessaging.CKA.FromLWE.Basic`), instantiating the abstract `CKAScheme`
interface. Here [ACD19] denotes Alwen, Coretti, and Dodis, *The Double Ratchet:
Security Notions, Proofs, and Modularization for the Signal Protocol*; the
construction is its optimized Frodo/LWE CKA of Section 4.1.2.

## Party roles

The repository CKA game starts from a `sendA` state. In ACD19's LWE
initialization, the first displayed half-round is paper-B sending from
`(A, B := A * S + E)` to paper-A, who receives using `(A, S)`. We align that
half-round with the repository's initial `sendA`/`recvB` transition: Lean
`sendA`/`recvB` implement paper `CKA-S-B`/`CKA-R-A`, and Lean `sendB`/`recvA`
implement paper `CKA-S-A`/`CKA-R-B`.

## States and messages

A party's local state records both its role (sender or receiver) and the key
material it currently holds:

* `sendAReady common pubAB` — A is about to send and holds its public key;
* `recvAReady common secBA` — A is about to receive and holds the secret matching
  the public key it last sent;
* `sendBReady common pubBA` — B is about to send and holds the public key it last
  received;
* `recvBReady common secAB` — B is about to receive and holds its secret.

A message is a fresh public key together with reconciliation information, tagged
by its direction: `fromA` for an A-to-B message and `fromB` for a B-to-A message.
The initial shared key material is the common value with A's first public key and
B's first secret, and the send randomness is the randomness of whichever party
sent, tagged by `Sum`.

The type aliases `Common`, `PubAB`, `PubBA`, `SecAB`, `SecBA`, `RandA`, and
`RandB` name the matrix entries of a `Frodo.MatrixParams`, so the state, message,
and scheme definitions read in protocol terms.
-/

open OracleSpec OracleComp

namespace lweCKA

/-- Common value: the public matrix `A`. -/
abbrev Common (p : Frodo.MatrixParams) := Frodo.Mat p.q p.n p.n
/-- Public key held by A before a send, matched by a `SecAB`. -/
abbrev PubAB (p : Frodo.MatrixParams) := Frodo.Mat p.q p.n p.nbar
/-- Public key produced by A's send and consumed by B's send. -/
abbrev PubBA (p : Frodo.MatrixParams) := Frodo.Mat p.q p.nbar p.n
/-- Secret held by B that pairs with a `PubAB`. -/
abbrev SecAB (p : Frodo.MatrixParams) := Frodo.Mat p.q p.n p.nbar
/-- Secret held by A that pairs with a `PubBA`. -/
abbrev SecBA (p : Frodo.MatrixParams) := Frodo.Mat p.q p.nbar p.n
/-- Randomness sampled by A's send: `S'`, `E'`, and `Etilde'`. -/
abbrev RandA (p : Frodo.MatrixParams) :=
  Frodo.Mat p.q p.nbar p.n × Frodo.Mat p.q p.nbar p.n × Frodo.Mat p.q p.nbar p.nbar
/-- Randomness sampled by B's send: `S''`, `E''`, and `Etilde''`. -/
abbrev RandB (p : Frodo.MatrixParams) :=
  Frodo.Mat p.q p.n p.nbar × Frodo.Mat p.q p.n p.nbar × Frodo.Mat p.q p.nbar p.nbar

/-- Phase- and direction-tagged CKA state for the Frodo/LWE construction.

Each constructor records the party, whether its next local action is a send or a
receive, and the key material it holds at that point. -/
inductive State (p : Frodo.MatrixParams) where
  /-- A is ready to send and holds its current public key. -/
  | sendAReady : Common p → PubAB p → State p
  /-- A is ready to receive and holds the secret matching the key it last sent. -/
  | recvAReady : Common p → SecBA p → State p
  /-- B is ready to send and holds the public key it last received. -/
  | sendBReady : Common p → PubBA p → State p
  /-- B is ready to receive and holds its current secret. -/
  | recvBReady : Common p → SecAB p → State p

/-- CKA messages produced by the Frodo/LWE construction.

A message carries a fresh public key and reconciliation information. The tag
records its direction so the receiver can reject a message sent in the wrong
orientation. -/
inductive Message (p : Frodo.MatrixParams) where
  /-- Message from A to B: a `PubBA` public key and paper `C'`. -/
  | fromA : PubBA p → p.RecInfo → Message p
  /-- Message from B to A: a `PubAB` public key and paper `C`. -/
  | fromB : PubAB p → p.RecInfo → Message p

/-- Initial shared key material: the common value, A's first public key, and B's
first secret. -/
abbrev InitKey (p : Frodo.MatrixParams) := Common p × PubAB p × SecAB p

/-- Send randomness: A's randomness on the left, B's on the right. -/
abbrev Rand (p : Frodo.MatrixParams) := Sum (RandA p) (RandB p)

/-- Initialize the party that sends first with the common value and its public key. -/
def initA (p : Frodo.MatrixParams) (ik : InitKey p) : State p :=
  .sendAReady ik.1 ik.2.1

/-- Initialize the party that receives first with the common value and its secret. -/
def initB (p : Frodo.MatrixParams) (ik : InitKey p) : State p :=
  .recvBReady ik.1 ik.2.2

/-- A's send.

From `sendAReady common pubAB`, run the Frodo send to obtain the epoch key, a
fresh public key `pubBA`, reconciliation information, and the secret `secBA`
kept for the next receive. Emit `fromA pubBA recInfo` and move to
`recvAReady common secBA`. Called outside the send phase, the algorithm returns
`none`. -/
def sendA (p : Frodo.MatrixParams) :
    State p → ProbComp (Option (p.Key × Message p × State p))
  | .sendAReady common pubAB => do
      let (key, pubBA, recInfo, secBA, _randA) ← p.sendA common pubAB
      return some (key, Message.fromA pubBA recInfo, State.recvAReady common secBA)
  | _ => return none

/-- Randomness-leaking version of A's send.

Same transition as `sendA`, but the output also records A's send randomness,
tagged with `Sum.inl`. -/
def sendA_rleak (p : Frodo.MatrixParams) :
    State p → ProbComp (Option (p.Key × Message p × State p × Rand p))
  | .sendAReady common pubAB => do
      let (key, pubBA, recInfo, secBA, randA) ← p.sendA common pubAB
      return some (key, Message.fromA pubBA recInfo, State.recvAReady common secBA, Sum.inl randA)
  | _ => return none

/-- A's receive.

From `recvAReady common secBA` and a `fromB pubAB recInfo` message, run the Frodo
receive to recover the epoch key, then move to `sendAReady common pubAB`, keeping
the public key just received. A wrong state or message orientation returns
`none`, as does a failed Frodo receive. -/
def recvA (p : Frodo.MatrixParams) :
    State p → Message p → Option (p.Key × State p)
  | .recvAReady common secBA, .fromB pubAB recInfo =>
      match p.recvA secBA pubAB recInfo with
      | some key => some (key, State.sendAReady common pubAB)
      | none => none
  | _, _ => none

/-- B's send.

From `sendBReady common pubBA`, run the Frodo send to obtain the epoch key, a
fresh public key `pubAB`, reconciliation information, and the secret `secAB`
kept for the next receive. Emit `fromB pubAB recInfo` and move to
`recvBReady common secAB`. Called outside the send phase, the algorithm returns
`none`. -/
def sendB (p : Frodo.MatrixParams) :
    State p → ProbComp (Option (p.Key × Message p × State p))
  | .sendBReady common pubBA => do
      let (key, pubAB, recInfo, secAB, _randB) ← p.sendB common pubBA
      return some (key, Message.fromB pubAB recInfo, State.recvBReady common secAB)
  | _ => return none

/-- Randomness-leaking version of B's send.

Same transition as `sendB`, but the output also records B's send randomness,
tagged with `Sum.inr`. -/
def sendB_rleak (p : Frodo.MatrixParams) :
    State p → ProbComp (Option (p.Key × Message p × State p × Rand p))
  | .sendBReady common pubBA => do
      let (key, pubAB, recInfo, secAB, randB) ← p.sendB common pubBA
      return some (key, Message.fromB pubAB recInfo, State.recvBReady common secAB, Sum.inr randB)
  | _ => return none

/-- B's receive.

From `recvBReady common secAB` and a `fromA pubBA recInfo` message, run the Frodo
receive to recover the epoch key, then move to `sendBReady common pubBA`, keeping
the public key just received. A wrong state or message orientation returns `none`,
as does a failed Frodo receive. -/
def recvB (p : Frodo.MatrixParams) :
    State p → Message p → Option (p.Key × State p)
  | .recvBReady common secAB, .fromA pubBA recInfo =>
      match p.recvB secAB pubBA recInfo with
      | some key => some (key, State.sendBReady common pubBA)
      | none => none
  | _, _ => none

/-- The Frodo/LWE CKA scheme over a `Frodo.MatrixParams`.

The type parameters instantiate the abstract CKA interface as follows:

* `IK = InitKey p`, the common matrix with A's first public key and B's first
  secret;
* `St = State p`, the phase- and direction-tagged local state;
* `I = p.Key`, the Frodo epoch key;
* `Rho = Message p`, the protocol-message space;
* `Rand = Rand p`, the per-send randomness of whichever party sent.

The send and receive algorithms are the matrix operations of `p`, assembled into
the side-specific state machine under the party-role naming described in the
module docstring. -/
-- ANCHOR: frodoScheme
def frodoScheme (p : Frodo.MatrixParams) :
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
-- ANCHOR_END: frodoScheme

end lweCKA
