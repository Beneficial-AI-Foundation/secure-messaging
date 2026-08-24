/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Basic
import SecureMessaging.SCKA.Defs

/-!
# ML-KEM Braid as an SCKA scheme

`scheme` packages the transitions from `MLKEMBraid.Basic` as an `SCKAScheme`. Both
parties run the same `send` and `receive`. `initA` and `initB` build their initial states,
and `sampleInitKey` draws their initial common value.

`sendRleak` discloses key-generation or first-stage encapsulation randomness through
`KEMScheme.IncrementalRandLeak`; the other branches reuse `send`. `recvSCKA` refuses a
delivery when `receive` returns a `Failure` and reports the message-derived epoch required
by SCKA. `Basic.receive` keeps the state-derived report from Braid §2.5.
-/

open ErasureCodePayload.Streaming

universe u

namespace MLKEMBraid

variable {m : Type → Type u} [Monad m] {P : Parameters m} {InitKey AuthState : Type}

/-- The randomness disclosed by a send. The second stage runs through `encaps2Det`, so the
transition system never discloses `IncrementalRandLeak.Encaps2Rand`. -/
-- ANCHOR: Braid_SendRand
inductive SendRand (KeygenRand Encaps1Rand : Type) where
  /-- The send ran neither `KeyGen` nor `Encaps1`. -/
  | none
  /-- The send ran `KeyGen`. -/
  | keygen (r : KeygenRand)
  /-- The send ran `Encaps1`. -/
  | encaps1 (r : Encaps1Rand)
-- ANCHOR_END: Braid_SendRand

/-- The send transition paired with its disclosed randomness. -/
-- ANCHOR: Braid_sendRleak
def sendRleak (P : Parameters m) (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) :
    m (SendResult P AuthState × SendRand irl.KeygenRand irl.Encaps1Rand)
-- ANCHOR_END: Braid_sendRleak
    :=
  match st with
  | .keysUnsampled e a => do
      let ((pk, sk), r) ← irl.keygenRleak
      let hdr := P.inc.toHeader pk
      let vec := P.inc.toVector pk
      let tag := auth.macHeader a e hdr
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
      pure ({ msg := { epoch := e, type := .hdr, data := some chunk },
              sendingEpoch := e - 1, outputKey := none,
              state := .keysSampled e a sk vec enc }, .keygen r)
  | .headerReceived e a hdr ekDecoder => do
      let ((encapsState, ct1, k), r) ← irl.encaps1Rleak hdr
      let ik := P.kdfOK k e
      let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
      pure ({ msg := { epoch := e, type := .ct1, data := some chunk },
              sendingEpoch := e - 1, outputKey := some (e, ik),
              state := .ct1Sampled e (auth.update a e ik) hdr encapsState ct1 enc ekDecoder },
            .encaps1 r)
  | st => (fun r => (r, .none)) <$> send P auth st

/-- Discarding the randomness disclosed by `sendRleak` gives `send`. -/
theorem send_eq_map_sendRleak [LawfulMonad m] (P : Parameters m)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) :
    send P auth st = Prod.fst <$> sendRleak P irl auth st := by
  cases st
  case keysUnsampled e a =>
    simp only [send, sendRleak, ← irl.keygen_fst, map_eq_pure_bind, bind_assoc, pure_bind]
  case headerReceived e a hdr ekDecoder =>
    simp only [send, sendRleak, ← irl.encaps1_fst, map_eq_pure_bind, bind_assoc, pure_bind]
  all_goals simp [send, sendRleak]

/-- The randomness disclosed by `sendRleak`, as a function of the entry state. -/
theorem map_snd_sendRleak [LawfulMonad m] (P : Parameters m)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) :
    Prod.snd <$> sendRleak P irl auth st =
      match st with
      | .keysUnsampled .. =>
          (fun out => SendRand.keygen out.2) <$> irl.keygenRleak
      | .headerReceived _ _ hdr _ =>
          (fun out => SendRand.encaps1 out.2) <$> irl.encaps1Rleak hdr
      | _ => pure .none := by
  cases st
  case keysUnsampled e a =>
    simp only [sendRleak, map_eq_pure_bind, bind_assoc, pure_bind]
  case headerReceived e a hdr ekDecoder =>
    simp only [sendRleak, map_eq_pure_bind, bind_assoc, pure_bind]
  all_goals simp [send, sendRleak]

/-- Adapt `receive` to SCKA. Failures refuse delivery; successes report the sender's epoch. -/
-- ANCHOR: Braid_recvSCKA
def recvSCKA (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × State P AuthState)
-- ANCHOR_END: Braid_recvSCKA
    :=
  match receive P auth st msg with
  | .error _ =>
      -- N.B. The Braid spec starts a new session after MAC verification fails.
      -- SCKA has no termination result. Here `none` refuses delivery and makes the
      -- correctness oracle reject the trace; it does not model renegotiation.
      none
  | .ok r =>
      -- N.B. For ignored off-epoch messages, this differs from literal §2.5.
      -- SCKA requires the receive epoch to match the message's recorded send epoch.
      -- Accepted transitions already report `msg.epoch - 1` under §2.5.
      some (r.outputKey, msg.epoch - 1, r.state)

/-- ML-KEM Braid as an `SCKAScheme`. Both parties run the same algorithms and differ
only in their initial state. -/
-- ANCHOR: Braid_scheme
def scheme (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)
-- ANCHOR_END: Braid_scheme
    :=
  let sendSCKA (st : State P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : State P AuthState) := do
    let (r, rand) ← sendRleak P irl auth st
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

end MLKEMBraid
