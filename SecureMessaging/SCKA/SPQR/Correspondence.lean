/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.SPQR.Construction

/-! # SPQR chunked protocol and the ML-KEM Braid transition system

`SPQR.Chunked` follows the SPQR implementation, while `MLKEMBraid` follows Signal's
specification. This module translates SPQR states, messages, and send results into `MLKEMBraid`
and proves where the two agree.

`PartyState.toMLKEMBraid` is field for field, with the stored encapsulation key replaced by its
vector. `Message.toMLKEMBraid` maps each payload constructor to its message type and always produces
a well-formed message. Initialisation agrees.

A send agrees after translation in every state except `ekSentCt1Received`. In that state the message
type is `ct1Ack` here and `none` in `MLKEMBraid` (`states.rs:182`); the state and report agree.

Receive is compared at the SCKA level, `SPQR.recvSCKA` against `MLKEMBraid.recvSCKA`. For an ignored
message the transition reports differ: `st.epoch - 1` there and `msg.epoch - 1` here. Both adapters
report `msg.epoch - 1` and refuse delivery on every failure. On a delivery that
`MLKEMBraid.receive` does not ignore, the outputs agree.

The divergences all lie on ignored deliveries. A standalone `ct1Ack` in
`ekReceivedCt1Sampled` and a plain `ek` chunk in `ct1Acknowledged` complete here. A future epoch
outside the `ct2Sampled` successor case fails here with `epochOutOfRange`. Their exact
characterisation and a relation between the two SCKA schemes are not part of this module.

There is no translation in the other direction: rebuilding an encapsulation key from its vector
needs a `validPK` witness.
-/

open ErasureCodePayload.Streaming

universe u

namespace SPQR.Chunked

variable {m : Type → Type u} [Monad m] {P : MLKEMBraid.Parameters m} {InitKey AuthState : Type}

/-- The `MLKEMBraid` message with the same epoch and chunk; the payload constructor becomes the
message type. -/
-- ANCHOR: Correspondence_Message_toMLKEMBraid
def Message.toMLKEMBraid {Sym : Type} (msg : Message Sym) : MLKEMBraid.Message Sym :=
  match msg.payload with
  | .none => ⟨msg.epoch, .none, none⟩
  | .hdr chunk => ⟨msg.epoch, .hdr, some chunk⟩
  | .ek chunk => ⟨msg.epoch, .ek, some chunk⟩
  | .ekCt1Ack chunk => ⟨msg.epoch, .ekCt1Ack, some chunk⟩
  | .ct1Ack => ⟨msg.epoch, .ct1Ack, none⟩
  | .ct1 chunk => ⟨msg.epoch, .ct1, some chunk⟩
  | .ct2 chunk => ⟨msg.epoch, .ct2, some chunk⟩
-- ANCHOR_END: Correspondence_Message_toMLKEMBraid

/-- The `MLKEMBraid` state with the same fields; the stored encapsulation key is replaced by its
vector. -/
-- ANCHOR: Correspondence_PartyState_toMLKEMBraid
def PartyState.toMLKEMBraid : PartyState P AuthState → MLKEMBraid.State P AuthState
  | .keysUnsampled core => .keysUnsampled core.ep core.authSt
  | .keysSampled core enc =>
      .keysSampled core.ep core.authSt core.sk (P.inc.toVector core.pk) enc
  | .headerSent core enc dec => .headerSent core.ep core.authSt core.sk dec enc
  | .ct1Received core enc => .ct1Received core.ep core.authSt core.sk core.c1 enc
  | .ekSentCt1Received core dec => .ekSentCt1Received core.ep core.authSt core.sk core.c1 dec
  | .noHeaderReceived core dec => .noHeaderReceived core.ep core.authSt dec
  | .headerReceived core dec => .headerReceived core.ep core.authSt core.hdr dec
  | .ct1Sampled core enc dec =>
      .ct1Sampled core.ep core.authSt core.hdr core.encapsSt core.c1 enc dec
  | .ekReceivedCt1Sampled core enc =>
      .ekReceivedCt1Sampled core.ep core.authSt core.encapsSt core.c1 core.hdr core.vec enc
  | .ct1Acknowledged core dec =>
      .ct1Acknowledged core.ep core.authSt core.hdr core.encapsSt core.c1 dec
  | .ct2Sampled core enc => .ct2Sampled core.ep core.authSt enc
-- ANCHOR_END: Correspondence_PartyState_toMLKEMBraid

/-- Translate the message and the state of a send result. -/
-- ANCHOR: Correspondence_SendResult_toMLKEMBraid
def SendResult.toMLKEMBraid (r : SendResult P AuthState) : MLKEMBraid.SendResult P AuthState :=
  ⟨r.msg.toMLKEMBraid, r.sendingEpoch, r.outputKey, r.state.toMLKEMBraid⟩
-- ANCHOR_END: Correspondence_SendResult_toMLKEMBraid

/-- Both models start direction A2B in the same state. -/
-- ANCHOR: Correspondence_toMLKEMBraid_initA
theorem toMLKEMBraid_initA (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac) (ik : InitKey) :
    (initA P auth ik).toMLKEMBraid = MLKEMBraid.initA P auth ik
-- ANCHOR_END: Correspondence_toMLKEMBraid_initA
    := rfl

/-- Both models start direction B2A in the same state. -/
-- ANCHOR: Correspondence_toMLKEMBraid_initB
theorem toMLKEMBraid_initB (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac) (ik : InitKey) :
    (initB P auth ik).toMLKEMBraid = MLKEMBraid.initB P auth ik
-- ANCHOR_END: Correspondence_toMLKEMBraid_initB
    := rfl

/-- Outside `ekSentCt1Received`, a send agrees with `MLKEMBraid.send` after translation. -/
-- ANCHOR: Correspondence_send_toMLKEMBraid
theorem send_toMLKEMBraid [LawfulMonad m] (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (h : ∀ core dec, st ≠ .ekSentCt1Received core dec) :
    SendResult.toMLKEMBraid <$> send P auth st = MLKEMBraid.send P auth st.toMLKEMBraid
-- ANCHOR_END: Correspondence_send_toMLKEMBraid
    := by
  cases st
  case keysUnsampled core =>
    simp only [send, MLKEMBraid.send, EkSender.sendHeader, map_eq_pure_bind, bind_assoc,
      pure_bind, SendResult.toMLKEMBraid, PartyState.toMLKEMBraid, Message.toMLKEMBraid]
  case headerReceived core dec =>
    simp only [send, MLKEMBraid.send, CtSender.sendCt1, map_eq_pure_bind, bind_assoc,
      pure_bind, SendResult.toMLKEMBraid, PartyState.toMLKEMBraid, Message.toMLKEMBraid]
  case ekSentCt1Received core dec => exact absurd rfl (h core dec)
  all_goals
    simp [send, MLKEMBraid.send, SendResult.toMLKEMBraid, PartyState.toMLKEMBraid,
      Message.toMLKEMBraid]

/-- In `ekSentCt1Received` the two sends differ only in the message type: `ct1Ack` here, `none` in
`MLKEMBraid` (`states.rs:182`). -/
-- ANCHOR: Correspondence_send_ekSentCt1Received_toMLKEMBraid
theorem send_ekSentCt1Received_toMLKEMBraid [LawfulMonad m]
    (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (core : EkSender.EkSentCt1Received P.inc AuthState)
    (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym) :
    SendResult.toMLKEMBraid <$> send P auth (.ekSentCt1Received core dec) =
      (fun r => { r with msg := ⟨r.msg.epoch, .ct1Ack, r.msg.data⟩ }) <$>
        MLKEMBraid.send P auth (PartyState.toMLKEMBraid (.ekSentCt1Received core dec))
-- ANCHOR_END: Correspondence_send_ekSentCt1Received_toMLKEMBraid
    := by
  simp [send, MLKEMBraid.send, SendResult.toMLKEMBraid, PartyState.toMLKEMBraid,
    Message.toMLKEMBraid]

end SPQR.Chunked

namespace SPQR

open Chunked

variable {m : Type → Type u} [Monad m] {InitKey AuthState : Type}

set_option maxHeartbeats 300000 in
-- The proof checks every state and payload pair and unfolds both receive functions, hence it
-- requires significant computation time.
set_option linter.flexible false in
/-- On a delivery that `MLKEMBraid.receive` does not ignore, the SCKA receive outputs agree after
translation. Every divergence between the two receives is on an ignored delivery. -/
-- ANCHOR: Correspondence_recvSCKA_toMLKEMBraid
theorem recvSCKA_toMLKEMBraid (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym)
    (h : MLKEMBraid.receive P auth st.toMLKEMBraid msg.toMLKEMBraid ≠
      .ok ⟨st.toMLKEMBraid.epoch - 1, none, st.toMLKEMBraid⟩) :
    (recvSCKA P auth st msg).map (fun r => (r.1, r.2.1, r.2.2.toMLKEMBraid)) =
      MLKEMBraid.recvSCKA P auth st.toMLKEMBraid msg.toMLKEMBraid
-- ANCHOR_END: Correspondence_recvSCKA_toMLKEMBraid
    := by
  obtain ⟨e, payload⟩ := msg
  cases st <;> cases payload <;>
    simp [recvSCKA, Chunked.recv, MLKEMBraid.recvSCKA, MLKEMBraid.receive,
      Chunked.PartyState.toMLKEMBraid, Chunked.Message.toMLKEMBraid,
      Chunked.PartyState.epoch, MLKEMBraid.State.epoch, MLKEMBraid.Message.wellFormed,
      Chunked.completeCt2, EkSender.sendVector, EkSender.recvCt1, EkSender.recvCt2,
      CtSender.recvHeader, CtSender.recvVector, CtSender.recvNextEpoch] at h ⊢ <;>
    split_ifs at h ⊢ <;> simp_all
  all_goals
    generalize hdec :
      (‹DecoderState _ _›.addChunk ‹ℕ × P.Sym›).decodedPayload = decoded at h ⊢
    cases decoded <;> simp_all
  all_goals try (split_ifs at h ⊢ <;> simp_all)
  all_goals
    generalize hdecaps : P.hDet.decapsDet _ _ = decaps at h ⊢
    cases decaps <;> simp_all
  all_goals try (split_ifs at h ⊢ <;> simp_all)

end SPQR
