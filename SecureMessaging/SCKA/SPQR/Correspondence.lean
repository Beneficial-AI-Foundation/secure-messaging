/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Construction

/-! # SPQR chunked protocol and the ML-KEM Braid transition system

`SPQR.Chunked` follows the SPQR implementation, while `Braid` follows Signal's
specification. This module translates SPQR states, messages, and send results into `Braid`
and proves where the two agree.

`PartyState.toBraid` is field for field, with the stored encapsulation key replaced by its
vector. `Message.toBraid` maps each payload constructor to the message type of the same name
and always produces a well-formed message. The one exception is `ct1Ack`, which becomes an empty
message: in `ekSentCt1Received` SPQR sends `Ct1Ack(true)` where `Braid` sends an empty
message (`states.rs:182`), and no `Braid` transition reads either type. With this translation,
initialisation and every send agree.

Receive is compared at the SCKA level, `SPQR.recvSCKA` against `Braid.recvSCKA`. For an ignored
message the transition reports differ: `st.epoch - 1` there and `msg.epoch - 1` here. Both adapters
report `msg.epoch - 1` and refuse delivery on every failure, so they agree on deliveries that both
ignore. The two receives agree on every delivery outside `RecvDivergence`, which has three cases:

* a future epoch other than the successor epoch of `ct2Sampled`: SPQR refuses it with
  `epochOutOfRange`, and `Braid` ignores it;
* a standalone `ct1Ack` in `ekReceivedCt1Sampled`: SPQR completes `ct₂`, and `Braid` ignores
  it;
* a plain `ek` chunk in `ct1Acknowledged`: SPQR adds the chunk to its vector decoder
  (`states.rs:487`), and `Braid` ignores it.

In the third case SPQR acts as `Braid` acts on the same chunk sent as an acknowledging vector
chunk (`recvSCKA_ct1Acknowledged_ek_toBraid`). `SPQR.Correctness.Relation` lifts these facts
to the correctness games. Under the invariants of the correctness proof the first two cases cannot
occur, and the third is handled by this relabelling.

There is no translation in the other direction: rebuilding an encapsulation key from its vector
needs a `validPK` witness.
-/

@[expose] public section

open ErasureCodePayload.Streaming

universe u

namespace SPQR.Chunked

variable {m : Type → Type u} [Monad m] {P : SPQR.Parameters m} {InitKey AuthState : Type}

/-- Translate a message into `Braid`; `ct1Ack` becomes an empty message. -/
-- ANCHOR: Correspondence_Message_toMLKEMBraid
def Message.toBraid {Sym : Type} (msg : Message Sym) : Braid.Message Sym :=
  match msg.payload with
  | .none => ⟨msg.epoch, .none, none⟩
  | .hdr chunk => ⟨msg.epoch, .hdr, some chunk⟩
  | .ek chunk => ⟨msg.epoch, .ek, some chunk⟩
  | .ekCt1Ack chunk => ⟨msg.epoch, .ekCt1Ack, some chunk⟩
  | .ct1Ack => ⟨msg.epoch, .none, none⟩
  | .ct1 chunk => ⟨msg.epoch, .ct1, some chunk⟩
  | .ct2 chunk => ⟨msg.epoch, .ct2, some chunk⟩
-- ANCHOR_END: Correspondence_Message_toMLKEMBraid

/-- The `Braid` state with the same fields; the stored encapsulation key is replaced by its
vector. -/
-- ANCHOR: Correspondence_PartyState_toMLKEMBraid
def PartyState.toBraid : PartyState P AuthState → Braid.State P.toBraid AuthState
  | .keysUnsampled core => .keysUnsampled core.ep core.authSt
  | .keysSampled core enc =>
      .keysSampled core.ep core.authSt core.sk (P.det.toVector core.pk) enc
  | .headerSent core enc dec => .headerSent core.ep core.authSt core.sk dec enc
  | .ct1Received core enc => .ct1Received core.ep core.authSt core.sk core.c1 enc
  | .ekSentCt1Received core dec => .ekSentCt1Received core.ep core.authSt core.sk core.c1 dec
  | .noHeaderReceived core dec => .noHeaderReceived core.ep core.authSt dec
  | .headerReceived core dec => .headerReceived core.ep core.authSt core.hdr dec
  | .ct1Sampled core enc dec =>
      .ct1Sampled core.ep core.authSt core.hdr core.encapsSt core.c1 enc dec
  | .ekReceivedCt1Sampled core enc =>
      .ekReceivedCt1Sampled core.ep core.authSt core.encapsSt core.c1 core.hdr core.ek enc
  | .ct1Acknowledged core dec =>
      .ct1Acknowledged core.ep core.authSt core.hdr core.encapsSt core.c1 dec
  | .ct2Sampled core enc => .ct2Sampled core.ep core.authSt enc
-- ANCHOR_END: Correspondence_PartyState_toMLKEMBraid

/-- Translate the message and the state of a send result. -/
-- ANCHOR: Correspondence_SendResult_toMLKEMBraid
def SendResult.toBraid (r : SendResult P AuthState) :
    Braid.SendResult P.toBraid AuthState :=
  ⟨r.msg.toBraid, r.sendingEpoch, r.outputKey, r.state.toBraid⟩
-- ANCHOR_END: Correspondence_SendResult_toMLKEMBraid

/-- Translating a message keeps its epoch. -/
@[simp] theorem Message.toBraid_epoch {Sym : Type} (msg : Message Sym) :
    msg.toBraid.epoch = msg.epoch := by
  obtain ⟨e, payload⟩ := msg
  cases payload <;> rfl

/-- Translating a state keeps its epoch. -/
@[simp] theorem PartyState.toBraid_epoch (st : PartyState P AuthState) :
    st.toBraid.epoch = st.epoch := by
  cases st <;> rfl

/-- Both models start direction A2B in the same state. -/
-- ANCHOR: Correspondence_toMLKEMBraid_initA
theorem toBraid_initA (P : SPQR.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (ik : InitKey) :
    (initA P auth ik).toBraid = Braid.initA P.toBraid auth ik
-- ANCHOR_END: Correspondence_toMLKEMBraid_initA
    := rfl

/-- Both models start direction B2A in the same state. -/
-- ANCHOR: Correspondence_toMLKEMBraid_initB
theorem toBraid_initB (P : SPQR.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (ik : InitKey) :
    (initB P auth ik).toBraid = Braid.initB P.toBraid auth ik
-- ANCHOR_END: Correspondence_toMLKEMBraid_initB
    := rfl

/-- A send agrees with `Braid.send` after translation. -/
-- ANCHOR: Correspondence_send_toMLKEMBraid
theorem send_toBraid [LawfulMonad m] (P : SPQR.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) :
    SendResult.toBraid <$> SPQR.send P auth st =
      Braid.send P.toBraid auth st.toBraid
-- ANCHOR_END: Correspondence_send_toMLKEMBraid
    := by
  rw [map_eq_pure_bind]
  cases st
  case keysUnsampled core =>
    simp only [SPQR.send, Chunked.send, Braid.send, EkSender.sendHeader,
      Parameters.generate, Parameters.toBraid, KEMScheme.IncrementalKEMDet.toKEM,
      map_eq_pure_bind, bind_assoc,
      pure_bind, SendResult.toBraid, PartyState.toBraid, Message.toBraid,
      KEMScheme.IncrementalKEMDet.toIncremental,
      KEMScheme.IncrementalStructure.toHeader, KEMScheme.IncrementalStructure.toVector,
      KEMScheme.IncrementalKEMDet.toHeader, KEMScheme.IncrementalKEMDet.toVector]
    rfl
  case headerReceived core dec =>
    simp only [SPQR.send, Chunked.send, Braid.send, CtSender.sendCt1,
      Parameters.encaps1, Parameters.toBraid, KEMScheme.IncrementalKEMDet.toIncremental,
      map_eq_pure_bind, bind_assoc, pure_bind, SendResult.toBraid,
      PartyState.toBraid, Message.toBraid, KEMScheme.IncrementalKEMDet.toVector]
  all_goals
    simp [SPQR.send, Chunked.send, Braid.send, SendResult.toBraid,
      PartyState.toBraid, Message.toBraid, Parameters.toBraid,
      KEMScheme.IncrementalKEMDet.toIncremental, KEMScheme.IncrementalKEMDet.toVector]

end SPQR.Chunked

namespace SPQR

open Chunked

variable {m : Type → Type u} [Monad m] {P : SPQR.Parameters m} {InitKey AuthState : Type}

/-- The deliveries on which `recvSCKA` and `Braid.recvSCKA` can disagree after translation. -/
-- ANCHOR: Correspondence_RecvDivergence
def RecvDivergence (st : PartyState P AuthState) (msg : Message P.Sym) : Prop :=
  (st.epoch < msg.epoch ∧ ¬ ((∃ core enc, st = .ct2Sampled core enc) ∧ msg.epoch = st.epoch + 1)) ∨
    (msg.epoch = st.epoch ∧ (∃ core enc, st = .ekReceivedCt1Sampled core enc) ∧
      msg.payload = .ct1Ack) ∨
    (msg.epoch = st.epoch ∧ (∃ core dec, st = .ct1Acknowledged core dec) ∧
      ∃ chunk, msg.payload = .ek chunk)
-- ANCHOR_END: Correspondence_RecvDivergence

/-- `Braid.receive` ignores a translated message whose epoch is below the receiver's. -/
private theorem receive_toBraid_of_lt
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) (hlt : msg.epoch < st.epoch) :
    Braid.receive P.toBraid auth st.toBraid msg.toBraid =
      .ok ⟨st.toBraid.epoch - 1, none, st.toBraid⟩ := by
  have hne : msg.epoch ≠ st.epoch := hlt.ne
  have hne' : msg.epoch ≠ st.epoch + 1 := by omega
  obtain ⟨e, payload⟩ := msg
  cases st <;> cases payload <;>
    simp_all [Braid.receive, Chunked.Message.toBraid, Chunked.PartyState.toBraid,
      Chunked.PartyState.epoch, Braid.Message.wellFormed]

set_option maxHeartbeats 300000 in
-- The proof checks every state and payload pair and unfolds both receive functions, hence it
-- requires significant computation time.
/-- At equal epochs and outside `RecvDivergence`, the SCKA receive outputs agree after
translation. -/
private theorem recvSCKA_toBraid_of_epoch_eq
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) (heq : msg.epoch = st.epoch)
    (h : ¬ RecvDivergence st msg) :
    (recvSCKA P auth st msg).map (fun (keyOpt, trcv, st') => (keyOpt, trcv, st'.toBraid)) =
      Braid.recvSCKA P.toBraid auth st.toBraid msg.toBraid := by
  obtain ⟨e, payload⟩ := msg
  dsimp only at heq
  subst heq
  cases st <;> cases payload <;>
    simp only [RecvDivergence, Chunked.Message.toBraid] at h ⊢ <;>
    simp only [recvSCKA, recv, Braid.recvSCKA, Braid.receive, PartyState.toBraid,
      PartyState.epoch, Braid.State.epoch, Braid.Message.wellFormed, completeCt2,
      EkSender.sendEk, EkSender.recvCt1, EkSender.recvCt2, CtSender.recvHeader,
      CtSender.recvEk, Parameters.encaps2, Parameters.decaps, Parameters.ekMatchesHeader,
      Parameters.toBraid, KEMScheme.IncrementalKEMDet.toDetDecaps,
      KEMScheme.IncrementalKEMDet.toDetEncaps2, KEMScheme.IncrementalKEMDet.toIncremental,
      KEMScheme.IncrementalKEMDet.toVector, PartyState.ct1Acknowledged.injEq,
      PartyState.ct2Sampled.injEq, PartyState.ekReceivedCt1Sampled.injEq, Payload.ek.injEq,
      Bool.false_eq_true, Bool.not_true, Nat.left_eq_add, Option.isNone_none, Option.isSome_some,
      Option.map_some, and_false, and_self, and_true, exists_and_left, exists_eq', exists_false,
      lt_self_iff_false, not_false_eq_true, not_true_eq_false, one_ne_zero, or_false, or_self,
      or_true, reduceCtorEq, ↓existsAndEq, ↓reduceIte] at h ⊢ <;>
    try simp_all only
  all_goals
    generalize hdec : StreamDecoder.decodedPayload _ (StreamDecoder.addChunk _ _ _) = decoded
    cases decoded <;> simp_all only [Option.map_some]
  all_goals try (split_ifs <;> simp_all)
  all_goals
    generalize hdecaps : P.det.decapsDet _ _ = decaps
    cases decaps <;> simp_all only [Option.map_none]
  all_goals try (split_ifs <;> simp_all)

/-- Outside `RecvDivergence`, the SCKA receive outputs agree after translation. This includes the
deliveries that both receives ignore: both adapters report `msg.epoch - 1` and keep the state. -/
-- ANCHOR: Correspondence_recvSCKA_toMLKEMBraid
theorem recvSCKA_toBraid (P : SPQR.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) (h : ¬ RecvDivergence st msg) :
    (recvSCKA P auth st msg).map (fun (keyOpt, trcv, st') => (keyOpt, trcv, st'.toBraid)) =
      Braid.recvSCKA P.toBraid auth st.toBraid msg.toBraid
-- ANCHOR_END: Correspondence_recvSCKA_toMLKEMBraid
    := by
  rcases lt_trichotomy msg.epoch st.epoch with hlt | heq | hgt
  · have hS : recv P auth st msg = .ok ⟨msg.epoch - 1, none, st⟩ := by
      simp [Chunked.recv, hlt]
    simp [recvSCKA, Braid.recvSCKA, hS, receive_toBraid_of_lt auth st msg hlt]
  · exact recvSCKA_toBraid_of_epoch_eq auth st msg heq h
  · -- A future epoch outside `RecvDivergence` is the successor epoch of `ct2Sampled`.
    obtain ⟨⟨core, enc, rfl⟩, hsucc⟩ : (∃ core enc, st = .ct2Sampled core enc) ∧
        msg.epoch = st.epoch + 1 := by
      by_contra hn
      exact h (Or.inl ⟨hgt, hn⟩)
    obtain ⟨e, payload⟩ := msg
    simp only [Chunked.PartyState.epoch] at hsucc
    subst hsucc
    cases payload <;>
      simp [recvSCKA, Chunked.recv, Braid.recvSCKA, Braid.receive,
        Chunked.Message.toBraid, Chunked.PartyState.toBraid, Chunked.PartyState.epoch,
        Braid.Message.wellFormed, CtSender.recvNextEpoch]

/-- In `ct1Acknowledged`, SPQR receives a plain vector chunk as `Braid` receives the same
chunk sent as an acknowledging vector chunk (`states.rs:487`). -/
theorem recvSCKA_ct1Acknowledged_ek_toBraid (P : SPQR.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (core : CtSender.Ct1Sent P AuthState) (dec : P.decEk.D)
    (chunk : ℕ × P.Sym) :
    (recvSCKA P auth (.ct1Acknowledged core dec) ⟨core.ep, .ek chunk⟩).map
        (fun (keyOpt, trcv, st') => (keyOpt, trcv, st'.toBraid)) =
      Braid.recvSCKA P.toBraid auth (PartyState.toBraid (.ct1Acknowledged core dec))
        ⟨core.ep, .ekCt1Ack, some chunk⟩
    := by
  simp only [recvSCKA, Chunked.recv, Braid.recvSCKA, Braid.receive,
    Chunked.PartyState.toBraid, Chunked.PartyState.epoch, Braid.Message.wellFormed,
    Chunked.completeCt2, CtSender.recvEk, Parameters.encaps2, Parameters.ekMatchesHeader,
    Parameters.toBraid, KEMScheme.IncrementalKEMDet.toDetEncaps2,
    KEMScheme.IncrementalKEMDet.toIncremental, lt_irrefl]
  cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
  | none => simp
  | some ek => by_cases hv : P.det.validPK core.hdr ek = true <;> simp [hv]

end SPQR
