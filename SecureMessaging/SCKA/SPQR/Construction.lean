/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import SecureMessaging.SCKA.MLKEMBraid.Construction
import SecureMessaging.SCKA.SPQR.Chunked

/-! # SPQR as an SCKA scheme

`SPQR.scheme` presents SPQR, given by the chunked transitions of `SPQR.Chunked`, as an
`SCKAScheme`, the interface of the SCKA correctness and security games. Both parties run the same
algorithms from different initial states:

- `initKeyGen` samples the initial key, and `initA` and `initB` derive the initial states;
- `sendA` and `sendB` are `send`, the chunked send;
- `sendArleak` and `sendBrleak` are `sendRleak`, the chunked send that also returns the coins it
  samples: key-generation coins from `keysUnsampled`, first-stage encapsulation coins from
  `headerReceived`, and none from every other state (`map_snd_sendRleak`);
- `recvA` and `recvB` are `recvSCKA`, the chunked receive with every error mapped to `none`.

The SCKA receive oracles `SCKAScheme.oracleRecvA` and `SCKAScheme.oracleRecvB` treat `none` on a
sent message as a correctness violation: they keep the receiver's state and set `correct` to
`false`, so `SCKAScheme.correctnessExp` returns `false`.

The model fixes protocol version 1. Signal's Rust implementation,
[SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet), also negotiates
the version at the start of a session and may downgrade it once to the peer's version, including
version 0, which disables SPQR.
-/

open ErasureCodePayload.Streaming
open MLKEMBraid (SendRand)

universe u

namespace SPQR

open Chunked

variable {m : Type → Type u} [Monad m] {InitKey AuthState : Type}

/-- The send transition, also returning the coins it samples. -/
-- ANCHOR: SPQR_sendRleak
def sendRleak (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) :
    m (SendResult P AuthState × SendRand P.det.KeygenRand P.det.Encaps1Rand) :=
  Chunked.send P auth st
-- ANCHOR_END: SPQR_sendRleak

/-- The send transition with its sampled coins discarded. -/
-- ANCHOR: SPQR_send
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) : m (SendResult P AuthState) :=
  Prod.fst <$> sendRleak P auth st
-- ANCHOR_END: SPQR_send

/-- Discarding the disclosed randomness gives the ordinary send. -/
theorem send_eq_map_sendRleak (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) :
    send P auth st = Prod.fst <$> sendRleak P auth st := rfl

/-- A send returns key-generation coins in `keysUnsampled`, first-stage coins in
`headerReceived`, and no coins in every other state. -/
theorem map_snd_sendRleak [LawfulMonad m] (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) :
    Prod.snd <$> sendRleak P auth st =
      match st with
      | .keysUnsampled _ => SendRand.keygen <$> P.det.sampleKeygen
      | .headerReceived _ _ => SendRand.encaps1 <$> P.det.sampleEncaps1
      | _ => pure .none := by
  cases st <;>
    simp only [sendRleak, Chunked.send, EkSender.sendHeader, CtSender.sendCt1,
      map_eq_pure_bind, bind_assoc, pure_bind]

/-- Adapt `Chunked.recv` to SCKA; an error refuses delivery and a success forwards its report. -/
-- ANCHOR: SPQR_recvSCKA
def recvSCKA (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × PartyState P AuthState) := match recv P auth st msg with
  | .error _ => none
  | .ok r => some (r.outputKey, r.receivingEpoch, r.state)
-- ANCHOR_END: SPQR_recvSCKA

/-- SPQR as an `SCKAScheme`; both parties use the same algorithms and distinct initial states. -/
-- ANCHOR: SPQR_scheme
def scheme (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (PartyState P AuthState) (PartyState P AuthState)
      P.EpochKey (Message P.Sym) (SendRand P.det.KeygenRand P.det.Encaps1Rand) :=
  let sendSCKA (st : PartyState P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : PartyState P AuthState) := do
    let (r, rand) ← sendRleak P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state, rand))
  { initKeyGen := sampleInitKey
    initA := fun ik => pure (initA P auth ik)
    initB := fun ik => pure (initB P auth ik)
    sendA := sendSCKA
    sendArleak := sendRleakSCKA
    recvA := recvSCKA P auth
    sendB := sendSCKA
    sendBrleak := sendRleakSCKA
    recvB := recvSCKA P auth }
-- ANCHOR_END: SPQR_scheme

end SPQR
