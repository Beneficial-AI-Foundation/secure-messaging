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
vector. `Message.toMLKEMBraid` maps each payload constructor to the message type of the same name
and always produces a well-formed message. The one exception is `ct1Ack`, which becomes an empty
message: in `ekSentCt1Received` SPQR sends `Ct1Ack(true)` where `MLKEMBraid` sends an empty
message (`states.rs:182`), and no `MLKEMBraid` transition reads either type. With this translation,
initialisation and every send agree.

Receive is compared at the SCKA level, `SPQR.recvSCKA` against `MLKEMBraid.recvSCKA`. For an ignored
message the transition reports differ: `st.epoch - 1` there and `msg.epoch - 1` here. Both adapters
report `msg.epoch - 1` and refuse delivery on every failure, so they agree on deliveries that both
ignore. The two receives agree on every delivery outside `RecvDivergence`, which has three cells:

* a future epoch other than the successor epoch of `ct2Sampled`: SPQR refuses it with
  `epochOutOfRange`, and `MLKEMBraid` ignores it;
* a standalone `ct1Ack` in `ekReceivedCt1Sampled`: SPQR completes `ct₂`, and `MLKEMBraid` ignores
  it;
* a plain `ek` chunk in `ct1Acknowledged`: SPQR adds the chunk to its vector decoder
  (`states.rs:487`), and `MLKEMBraid` ignores it.

In the third cell SPQR acts as `MLKEMBraid` acts on the same chunk sent as an acknowledging vector
chunk (`recvSCKA_ct1Acknowledged_ek_toMLKEMBraid`). `SPQR.Correctness.Relation` lifts these facts
to the correctness games. There the first two cells cannot occur, and the third is handled by this
relabelling.

There is no translation in the other direction: rebuilding an encapsulation key from its vector
needs a `validPK` witness.
-/

open ErasureCodePayload.Streaming

universe u

namespace SPQR.Chunked

variable {m : Type → Type u} [Monad m] {P : MLKEMBraid.Parameters m} {InitKey AuthState : Type}

/-- The `MLKEMBraid` message with the same epoch and chunk. Each payload constructor becomes the
message type of the same name, except `ct1Ack`, which becomes an empty message: where SPQR sends
`Ct1Ack(true)`, `MLKEMBraid` sends an empty message (`states.rs:182`). -/
-- ANCHOR: Correspondence_Message_toMLKEMBraid
def Message.toMLKEMBraid {Sym : Type} (msg : Message Sym) : MLKEMBraid.Message Sym :=
  match msg.payload with
  | .none => ⟨msg.epoch, .none, none⟩
  | .hdr chunk => ⟨msg.epoch, .hdr, some chunk⟩
  | .ek chunk => ⟨msg.epoch, .ek, some chunk⟩
  | .ekCt1Ack chunk => ⟨msg.epoch, .ekCt1Ack, some chunk⟩
  | .ct1Ack => ⟨msg.epoch, .none, none⟩
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

/-- A send agrees with `MLKEMBraid.send` after translation. -/
-- ANCHOR: Correspondence_send_toMLKEMBraid
theorem send_toMLKEMBraid [LawfulMonad m] (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) :
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
  all_goals
    simp [send, MLKEMBraid.send, SendResult.toMLKEMBraid, PartyState.toMLKEMBraid,
      Message.toMLKEMBraid]

end SPQR.Chunked

namespace SPQR

open Chunked

variable {m : Type → Type u} [Monad m] {P : MLKEMBraid.Parameters m} {InitKey AuthState : Type}

/-- The deliveries on which `recvSCKA` and `MLKEMBraid.recvSCKA` can disagree after translation:
a future epoch other than the successor epoch of `ct2Sampled`, which SPQR refuses and
`MLKEMBraid` ignores; a standalone `ct1Ack` in `ekReceivedCt1Sampled`; and a plain `ek` chunk in
`ct1Acknowledged`. SPQR accepts the last two and `MLKEMBraid` ignores them. -/
-- ANCHOR: Correspondence_RecvDivergence
def RecvDivergence (st : PartyState P AuthState) (msg : Message P.Sym) : Prop :=
  (st.epoch < msg.epoch ∧ ¬ ((∃ core enc, st = .ct2Sampled core enc) ∧ msg.epoch = st.epoch + 1)) ∨
    (msg.epoch = st.epoch ∧ (∃ core enc, st = .ekReceivedCt1Sampled core enc) ∧
      msg.payload = .ct1Ack) ∨
    (msg.epoch = st.epoch ∧ (∃ core dec, st = .ct1Acknowledged core dec) ∧
      ∃ chunk, msg.payload = .ek chunk)
-- ANCHOR_END: Correspondence_RecvDivergence

/-- `MLKEMBraid.receive` ignores a translated message whose epoch is below the receiver's. -/
private theorem receive_toMLKEMBraid_of_lt [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) (hlt : msg.epoch < st.epoch) :
    MLKEMBraid.receive P auth st.toMLKEMBraid msg.toMLKEMBraid =
      .ok ⟨st.toMLKEMBraid.epoch - 1, none, st.toMLKEMBraid⟩ := by
  have hne : msg.epoch ≠ st.epoch := hlt.ne
  have hne' : msg.epoch ≠ st.epoch + 1 := by omega
  obtain ⟨e, payload⟩ := msg
  cases st <;> cases payload <;>
    simp_all [MLKEMBraid.receive, Chunked.Message.toMLKEMBraid, Chunked.PartyState.toMLKEMBraid,
      Chunked.PartyState.epoch, MLKEMBraid.Message.wellFormed]

set_option maxHeartbeats 300000 in
-- The proof checks every state and payload pair and unfolds both receive functions, hence it
-- requires significant computation time.
set_option linter.flexible false in
/-- At equal epochs and outside `RecvDivergence`, the SCKA receive outputs agree after
translation. -/
private theorem recvSCKA_toMLKEMBraid_of_epoch_eq [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) (heq : msg.epoch = st.epoch)
    (h : ¬ RecvDivergence st msg) :
    (recvSCKA P auth st msg).map (fun r => (r.1, r.2.1, r.2.2.toMLKEMBraid)) =
      MLKEMBraid.recvSCKA P auth st.toMLKEMBraid msg.toMLKEMBraid := by
  obtain ⟨e, payload⟩ := msg
  dsimp only at heq
  subst heq
  cases st <;> cases payload <;>
    simp only [RecvDivergence, Chunked.Message.toMLKEMBraid] at h ⊢ <;>
    simp [recvSCKA, Chunked.recv, MLKEMBraid.recvSCKA, MLKEMBraid.receive,
      Chunked.PartyState.toMLKEMBraid,
      Chunked.PartyState.epoch, MLKEMBraid.State.epoch, MLKEMBraid.Message.wellFormed,
      Chunked.completeCt2, EkSender.sendVector, EkSender.recvCt1, EkSender.recvCt2,
      CtSender.recvHeader, CtSender.recvVector] at h ⊢ <;>
    try simp_all
  all_goals
    generalize hdec : (‹DecoderState _ _›.addChunk ‹ℕ × P.Sym›).decodedPayload = decoded
    cases decoded <;> simp_all
  all_goals try (split_ifs <;> simp_all)
  all_goals
    generalize hdecaps : P.hDet.decapsDet _ _ = decaps
    cases decaps <;> simp_all
  all_goals try (split_ifs <;> simp_all)

/-- Outside `RecvDivergence`, the SCKA receive outputs agree after translation. This includes the
deliveries that both receives ignore: both adapters report `msg.epoch - 1` and keep the state. -/
-- ANCHOR: Correspondence_recvSCKA_toMLKEMBraid
theorem recvSCKA_toMLKEMBraid (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) (h : ¬ RecvDivergence st msg) :
    (recvSCKA P auth st msg).map (fun r => (r.1, r.2.1, r.2.2.toMLKEMBraid)) =
      MLKEMBraid.recvSCKA P auth st.toMLKEMBraid msg.toMLKEMBraid
-- ANCHOR_END: Correspondence_recvSCKA_toMLKEMBraid
    := by
  have hepoch : msg.toMLKEMBraid.epoch = msg.epoch := by
    obtain ⟨e, payload⟩ := msg
    cases payload <;> rfl
  rcases lt_trichotomy msg.epoch st.epoch with hlt | heq | hgt
  · have hS : recv P auth st msg = .ok ⟨msg.epoch - 1, none, st⟩ := by
      simp [Chunked.recv, hlt]
    simp [recvSCKA, MLKEMBraid.recvSCKA, hS, receive_toMLKEMBraid_of_lt auth st msg hlt, hepoch]
  · exact recvSCKA_toMLKEMBraid_of_epoch_eq auth st msg heq h
  · -- A future epoch outside `RecvDivergence` is the successor epoch of `ct2Sampled`.
    obtain ⟨⟨core, enc, rfl⟩, hsucc⟩ : (∃ core enc, st = .ct2Sampled core enc) ∧
        msg.epoch = st.epoch + 1 := by
      by_contra hn
      exact h (Or.inl ⟨hgt, hn⟩)
    obtain ⟨e, payload⟩ := msg
    simp only [Chunked.PartyState.epoch] at hsucc
    subst hsucc
    cases payload <;>
      simp [recvSCKA, Chunked.recv, MLKEMBraid.recvSCKA, MLKEMBraid.receive,
        Chunked.Message.toMLKEMBraid, Chunked.PartyState.toMLKEMBraid, Chunked.PartyState.epoch,
        MLKEMBraid.Message.wellFormed, CtSender.recvNextEpoch]

/-- In `ct1Acknowledged`, SPQR receives a plain vector chunk as `MLKEMBraid` receives the same
chunk sent as an acknowledging vector chunk (`states.rs:487`). -/
-- ANCHOR: Correspondence_recvSCKA_ct1Acknowledged_ek_toMLKEMBraid
theorem recvSCKA_ct1Acknowledged_ek_toMLKEMBraid (P : MLKEMBraid.Parameters m)
    [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (core : CtSender.Ct1Sent P.inc AuthState) (dec : DecoderState P.inc.PKvector P.Sym)
    (chunk : ℕ × P.Sym) :
    (recvSCKA P auth (.ct1Acknowledged core dec) ⟨core.ep, .ek chunk⟩).map
        (fun r => (r.1, r.2.1, r.2.2.toMLKEMBraid)) =
      MLKEMBraid.recvSCKA P auth (PartyState.toMLKEMBraid (.ct1Acknowledged core dec))
        ⟨core.ep, .ekCt1Ack, some chunk⟩
-- ANCHOR_END: Correspondence_recvSCKA_ct1Acknowledged_ek_toMLKEMBraid
    := by
  simp only [recvSCKA, Chunked.recv, MLKEMBraid.recvSCKA, MLKEMBraid.receive,
    Chunked.PartyState.toMLKEMBraid, Chunked.PartyState.epoch, MLKEMBraid.Message.wellFormed,
    Chunked.completeCt2, CtSender.recvVector, lt_irrefl]
  cases (dec.addChunk chunk).decodedPayload <;> simp
  split_ifs <;> simp

end SPQR
