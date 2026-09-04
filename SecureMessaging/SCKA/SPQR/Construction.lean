/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import SecureMessaging.SCKA.MLKEMBraid.Construction
import SecureMessaging.SCKA.SPQR.Chunked

/-! # SPQR as an SCKA scheme

`SPQR.scheme` packages the chunked transitions as an `SCKAScheme` without changing them. A receive
error maps to `none`, which refuses delivery and makes the SCKA correctness oracle reject the trace
(`SCKA/Defs.lean:511-514`). It cannot trigger renegotiation.

The leak label is `.keygen` exactly in `keysUnsampled`, `.encaps1` exactly in `headerReceived`, and
`.none` elsewhere. Stage two discloses nothing because `P.hEnc2` is pure. The two restated arms
mirror `EkSender.sendHeader` and `CtSender.sendCt1`, and the projection theorem forces agreement
with `Chunked.send`.
-/

open ErasureCodePayload.Streaming
open MLKEMBraid (SendRand)

universe u

namespace SPQR

open Chunked

variable {m : Type → Type u} [Monad m] {InitKey AuthState : Type}

/-- `Chunked.send` paired with the disclosed randomness. -/
-- ANCHOR: SPQR_sendRleak
def sendRleak (P : MLKEMBraid.Parameters m) (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) :
    m (SendResult P AuthState × SendRand irl.KeygenRand irl.Encaps1Rand)
-- ANCHOR_END: SPQR_sendRleak
    := match st with
  | .keysUnsampled core => do
      let ((pk, sk), r) ← irl.keygenRleak
      let hdr := P.inc.toHeader pk
      let tag := auth.macHeader core.authSt core.ep hdr
      let core' : EkSender.HeaderSent P.inc AuthState :=
        ⟨core.ep, core.authSt, pk, sk⟩
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
      pure (⟨⟨core.ep, .hdr chunk⟩, core.ep - 1, none, .keysSampled core' enc⟩, .keygen r)
  | .headerReceived core dec => do
      let ((encapsSt, c1, k), r) ← irl.encaps1Rleak core.hdr
      let ik := P.kdfOK k core.ep
      let core' : CtSender.Ct1Sent P.inc AuthState :=
        ⟨core.ep, auth.update core.authSt core.ep ik, core.hdr, encapsSt, c1⟩
      let (chunk, enc) := (EncoderState.init P.ecpCt1 c1).nextChunk
      pure (⟨⟨core.ep, .ct1 chunk⟩, core.ep - 1, some (core.ep, ik),
        .ct1Sampled core' enc dec⟩, .encaps1 r)
  | _ => (fun r => (r, .none)) <$> send P auth st

/-- Discarding the disclosed randomness gives `Chunked.send`. -/
theorem send_eq_map_sendRleak [LawfulMonad m] (P : MLKEMBraid.Parameters m)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) :
    send P auth st = Prod.fst <$> sendRleak P irl auth st := by
  cases st
  case keysUnsampled core =>
    simp only [send, sendRleak, EkSender.sendHeader, ← irl.keygen_fst, map_eq_pure_bind,
      bind_assoc, pure_bind]
  case headerReceived core dec =>
    simp only [send, sendRleak, CtSender.sendCt1, ← irl.encaps1_fst, map_eq_pure_bind,
      bind_assoc, pure_bind]
  all_goals simp [send, sendRleak]

/-- The disclosed randomness as a function of the entry state. -/
theorem map_snd_sendRleak [LawfulMonad m] (P : MLKEMBraid.Parameters m)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) :
    Prod.snd <$> sendRleak P irl auth st =
      match st with
      | .keysUnsampled _ => (fun out => SendRand.keygen out.2) <$> irl.keygenRleak
      | .headerReceived core _ => (fun out => SendRand.encaps1 out.2) <$> irl.encaps1Rleak core.hdr
      | _ => pure .none := by
  cases st
  case keysUnsampled core =>
    simp only [sendRleak, map_eq_pure_bind, bind_assoc, pure_bind]
  case headerReceived core dec =>
    simp only [sendRleak, map_eq_pure_bind, bind_assoc, pure_bind]
  all_goals simp [send, sendRleak]

/-- Adapt `Chunked.recv` to SCKA; an error refuses delivery and a success forwards its report. -/
-- ANCHOR: SPQR_recvSCKA
def recvSCKA (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × PartyState P AuthState)
-- ANCHOR_END: SPQR_recvSCKA
    := match recv P auth st msg with
  | .error _ => none
  | .ok r => some (r.outputKey, r.receivingEpoch, r.state)

/-- SPQR as an `SCKAScheme`; both parties use the same algorithms and distinct initial states. -/
-- ANCHOR: SPQR_scheme
def scheme (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (PartyState P AuthState) (PartyState P AuthState)
      P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand) :=
  let sendSCKA (st : PartyState P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : PartyState P AuthState) := do
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
-- ANCHOR_END: SPQR_scheme

end SPQR
