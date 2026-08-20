/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Basic
import SecureMessaging.SCKA.Defs

/-!
# ML-KEM Braid as an SCKA scheme

`MLKEMBraid.Basic` packaged as an `SCKAScheme`: both parties run the same `send` and
`receive`, `initA` and `initB` build the two initial states, and `sampleInitKey` draws
the initial common value.

`SCKAScheme` asks for a randomness-leaking send. `RandLeak` supplies versions of
`KeyGen` and `Encaps1` that expose their sampled randomness. `sendRleak` uses them in the
`keysUnsampled` and `headerReceived` branches and delegates the other nine branches to
`send`. Its two projection theorems establish agreement with `send` and characterize the
disclosed randomness.

`recvSCKA` reports `msg.epoch - 1` in place of the state-derived report of `receive`, and
maps a `Failure` to the outer `none`, which the game reads as a refusal of the delivery;
an absent epoch key is the separate inner `none`. The game replays recorded messages in
any order and asserts `t^rcv = t^snd` on each delivery (`assertMatchingEpoch` in
`SCKAScheme.oracleRecvA`). Every send stamps `msg.epoch = state.epoch` and reports
`state.epoch - 1`, so `msg.epoch - 1` is exactly the sending epoch recorded with that
message. The two rules agree whenever a guard accepts, since the guards force
`msg.epoch = state.epoch`, and on `ct2Sampled` acceptance the post-transition report is
again `msg.epoch - 1`; they differ on ignored messages of another epoch, which the
state-derived rule reports with the receiver's epoch instead of the sender's.
-/

open ErasureCodePayload.Streaming

universe u

namespace MLKEMBraid

variable {m : Type → Type u} [Monad m] {P : Parameters m} {InitKey AuthState : Type}

/-- The randomness a send discloses. -/
-- ANCHOR: Braid_SendRand
inductive SendRand (KeygenRand Encaps1Rand : Type) where
  /-- The send ran neither `KeyGen` nor `Encaps1`. -/
  | none
  /-- The send ran `KeyGen`. -/
  | keygen (r : KeygenRand)
  /-- The send ran `Encaps1`. -/
  | encaps1 (r : Encaps1Rand)
-- ANCHOR_END: Braid_SendRand

/-- `KeyGen` and `Encaps1` returning the randomness they drew, with the equations
identifying their first component with the operation of `P`. -/
-- ANCHOR: Braid_RandLeak
structure RandLeak (P : Parameters m) where
  /-- Randomness space of `KeyGen`. -/
  KeygenRand : Type
  /-- Randomness space of `Encaps1`. -/
  Encaps1Rand : Type
  /-- `KeyGen` with its randomness. -/
  keyGenRleak : m ((P.Dk × P.EkSeed × P.EkVector) × KeygenRand)
  /-- `Encaps1` with its randomness. -/
  encaps1Rleak : P.EkSeed → P.Hek →
    m ((P.EncapsSecret × P.Ct1 × P.SharedSecret) × Encaps1Rand)
  /-- Discarding the randomness of `keyGenRleak` gives `P.keyGen`. -/
  keyGen_fst : (do let out ← keyGenRleak; pure out.1) = P.keyGen
  /-- Discarding the randomness of `encaps1Rleak` gives `P.encaps1`. -/
  encaps1_fst : ∀ seed hek,
    (do let out ← encaps1Rleak seed hek; pure out.1) = P.encaps1 seed hek
-- ANCHOR_END: Braid_RandLeak

/-- The send transition paired with its disclosed randomness. -/
-- ANCHOR: Braid_sendRleak
def sendRleak (P : Parameters m) (rl : RandLeak P)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) :
    m (SendResult P AuthState × SendRand rl.KeygenRand rl.Encaps1Rand) :=
  match st with
  | .keysUnsampled e a => do
      let ((dk, ekSeed, ekVector), r) ← rl.keyGenRleak
      let hek := P.hashEk ekSeed ekVector
      let tag := auth.macHeader a e (ekSeed, hek)
      let (chunk, enc) := (EncoderState.init P.ecpHdr ((ekSeed, hek), tag)).nextChunk
      pure ({ msg := { epoch := e, type := .hdr, data := some chunk },
              sendingEpoch := e - 1, outputKey := none,
              state := .keysSampled e a dk ekVector enc }, .keygen r)
  | .headerReceived e a ekSeed hek ekDecoder => do
      let ((encapsSecret, ct1, sharedSecret), r) ← rl.encaps1Rleak ekSeed hek
      let ik := P.kdfOK sharedSecret e
      let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
      pure ({ msg := { epoch := e, type := .ct1, data := some chunk },
              sendingEpoch := e - 1, outputKey := some (e, ik),
              state := .ct1Sampled e (auth.update a e ik) ekSeed hek encapsSecret ct1 enc
                ekDecoder }, .encaps1 r)
  | st => (fun r => (r, .none)) <$> send P auth st
-- ANCHOR_END: Braid_sendRleak

/-- Discarding the randomness disclosed by `sendRleak` gives `send`. -/
theorem send_eq_map_sendRleak [LawfulMonad m] (P : Parameters m) (rl : RandLeak P)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) :
    send P auth st = Prod.fst <$> sendRleak P rl auth st := by
  cases st
  case keysUnsampled e a =>
    simp only [send, sendRleak, ← rl.keyGen_fst, map_eq_pure_bind, bind_assoc, pure_bind]
  case headerReceived e a ekSeed hek ekDecoder =>
    simp only [send, sendRleak, ← rl.encaps1_fst, map_eq_pure_bind, bind_assoc, pure_bind]
  all_goals simp [send, sendRleak]

/-- The randomness disclosed by `sendRleak`, as a function of the entry state. -/
theorem map_snd_sendRleak [LawfulMonad m] (P : Parameters m) (rl : RandLeak P)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) :
    Prod.snd <$> sendRleak P rl auth st =
      match st with
      | .keysUnsampled .. =>
          (fun out => SendRand.keygen out.2) <$> rl.keyGenRleak
      | .headerReceived _ _ ekSeed hek _ =>
          (fun out => SendRand.encaps1 out.2) <$> rl.encaps1Rleak ekSeed hek
      | _ => pure .none := by
  cases st
  case keysUnsampled e a =>
    simp only [sendRleak, map_eq_pure_bind, bind_assoc, pure_bind]
  case headerReceived e a ekSeed hek ekDecoder =>
    simp only [sendRleak, map_eq_pure_bind, bind_assoc, pure_bind]
  all_goals simp [send, sendRleak]

/-- `receive` in the shape the SCKA game expects: a `Failure` becomes the outer `none`,
the game's refusal of the delivery, and the receive epoch reported is `msg.epoch - 1`,
the sending epoch recorded with the message. -/
-- ANCHOR: Braid_recvSCKA
def recvSCKA (P : Parameters m) [DecidableEq P.Sym] [DecidableEq P.Hek]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × State P AuthState) :=
  match receive P auth st msg with
  | .error _ => none
  | .ok r => some (r.outputKey, msg.epoch - 1, r.state)
-- ANCHOR_END: Braid_recvSCKA

/-- ML-KEM Braid as an `SCKAScheme`. Both parties run the same algorithms and differ
only in their initial state. -/
-- ANCHOR: Braid_scheme
def scheme (P : Parameters m) [DecidableEq P.Sym] [DecidableEq P.Hek]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (rl : RandLeak P) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym) (SendRand rl.KeygenRand rl.Encaps1Rand) :=
  let sendSCKA (st : State P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : State P AuthState) := do
    let (r, rand) ← sendRleak P rl auth st
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
-- ANCHOR_END: Braid_scheme

end MLKEMBraid
