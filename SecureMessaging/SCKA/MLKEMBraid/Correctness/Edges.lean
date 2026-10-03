/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Construction

/-!
# The edges of the Braid state machine

`SendEdge st r` enumerates the results `r` of `send` from the state `st`, one constructor per
state (`mem_support_send_iff`). `ReceiveEdge st msg r` enumerates the results of `receive` that
accept a message, one constructor per edge of Figure 1 of the specification plus `ignore`
(`ReceiveEdge.of_eq_ok`). The relation does not restate the guards of `ignore` and of edge 13, so
it may hold for a transition that `receive` does not take; the proofs only use the direction from
`receive` to the relation.

Proofs about one step of the protocol are case analyses on these relations. The module also
defines the two projections of a state that the invariants of the correctness proof measure, the
completed epoch and the control position, and proves how one edge changes them.
-/

open ErasureCodePayload.Streaming OracleComp

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-! ### Projections of a state -/

/-- The last epoch whose key the party has computed. An encapsulator from `ct1Sampled` on has
finished its own epoch; every other state has finished only the previous one. -/
def State.completedEpoch : State P AuthState → ℕ
  | .ct1Sampled e .. => e
  | .ekReceivedCt1Sampled e .. => e
  | .ct1Acknowledged e .. => e
  | .ct2Sampled e .. => e
  | st => st.epoch - 1

/-- A party's completed epoch is at most its epoch. -/
theorem State.completedEpoch_le_epoch (st : State P AuthState) :
    st.completedEpoch ≤ st.epoch := by
  cases st <;> simp [State.completedEpoch, State.epoch]

/-- A party has completed at least the epoch before its own. -/
theorem State.epoch_sub_one_le_completedEpoch (st : State P AuthState) :
    st.epoch - 1 ≤ st.completedEpoch := by
  cases st <;> simp [State.completedEpoch, State.epoch]

/-- A party's position within its epoch: its role and the step it has reached. -/
@[ext] structure ControlPosition where
  /-- `true` in the key-generating states and `false` in the encapsulating states. -/
  isGenerator : Bool
  /-- The step within that role, from `0` to `4`. -/
  step : ℕ
  deriving DecidableEq

/-- The position of a state within its epoch. The generator's steps are `keysUnsampled`,
`keysSampled`, `headerSent`, `ct1Received`, `ekSentCt1Received`; the encapsulator's are
`noHeaderReceived`, `headerReceived`, `ct1Sampled`, then `ekReceivedCt1Sampled` or
`ct1Acknowledged`, then `ct2Sampled`. -/
def State.controlPosition : State P AuthState → ControlPosition
  | .keysUnsampled .. => ⟨true, 0⟩
  | .keysSampled .. => ⟨true, 1⟩
  | .headerSent .. => ⟨true, 2⟩
  | .ct1Received .. => ⟨true, 3⟩
  | .ekSentCt1Received .. => ⟨true, 4⟩
  | .noHeaderReceived .. => ⟨false, 0⟩
  | .headerReceived .. => ⟨false, 1⟩
  | .ct1Sampled .. => ⟨false, 2⟩
  | .ekReceivedCt1Sampled .. => ⟨false, 3⟩
  | .ct1Acknowledged .. => ⟨false, 3⟩
  | .ct2Sampled .. => ⟨false, 4⟩

/-- The completed epoch in terms of the control position: an encapsulator from step `2` on has
completed its epoch; every other party has completed only the previous one. -/
theorem State.completedEpoch_eq (st : State P AuthState) :
    st.completedEpoch =
      if st.controlPosition.isGenerator = false ∧ 2 ≤ st.controlPosition.step then st.epoch
      else st.epoch - 1 := by
  cases st <;> simp [State.completedEpoch, State.controlPosition, State.epoch]

/-- The step of a state is at most `4`. -/
theorem State.controlPosition_step_le (st : State P AuthState) :
    st.controlPosition.step ≤ 4 := by
  cases st <;> simp [State.controlPosition]

/-- An encapsulator at step `4` is in `ct2Sampled`. -/
theorem State.eq_ct2Sampled_of_controlPosition (st : State P AuthState)
    (h : st.controlPosition = ⟨false, 4⟩) :
    ∃ a enc, st = .ct2Sampled st.epoch a enc := by
  cases st <;> simp [State.controlPosition] at h
  exact ⟨_, _, rfl⟩

/-! ### Send edges -/

/-- The results of `send`, one constructor per state. `keygen` (edge 1) and `encaps1` (edge 7)
sample; every other send is deterministic and emits the next chunk of the current stream, or an
empty `none` message in the three states that have nothing to send. -/
inductive SendEdge : State P AuthState → SendResult P AuthState → Prop
  /-- Edge 1: sample a key pair and emit the first header chunk. -/
  | keygen (e : ℕ) (a : AuthState) (pk : P.PK) (sk : P.SK)
      (h : (pk, sk) ∈ support P.kem.keygen) :
      SendEdge (.keysUnsampled e a)
        ⟨⟨e, .hdr, some (EncoderState.init P.ecpHdr
            (P.inc.toHeader pk, auth.macHeader a e (P.inc.toHeader pk))).nextChunk.1⟩,
          e - 1, none,
          .keysSampled e a sk (P.inc.toVector pk) (EncoderState.init P.ecpHdr
            (P.inc.toHeader pk, auth.macHeader a e (P.inc.toHeader pk))).nextChunk.2⟩
  /-- Emit the next header chunk. -/
  | hdrChunk (e : ℕ) (a : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
      (enc : EncoderState (P.inc.PKheader × P.Mac) P.Sym) :
      SendEdge (.keysSampled e a sk vec enc)
        ⟨⟨e, .hdr, some enc.nextChunk.1⟩, e - 1, none, .keysSampled e a sk vec enc.nextChunk.2⟩
  /-- Emit the next vector chunk. -/
  | ekChunk (e : ℕ) (a : AuthState) (sk : P.SK) (dec : DecoderState P.inc.C₁ P.Sym)
      (enc : EncoderState P.inc.PKvector P.Sym) :
      SendEdge (.headerSent e a sk dec enc)
        ⟨⟨e, .ek, some enc.nextChunk.1⟩, e - 1, none, .headerSent e a sk dec enc.nextChunk.2⟩
  /-- Emit the next vector chunk, acknowledging `ct₁`. -/
  | ackChunk (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (enc : EncoderState P.inc.PKvector P.Sym) :
      SendEdge (.ct1Received e a sk ct1 enc)
        ⟨⟨e, .ekCt1Ack, some enc.nextChunk.1⟩, e - 1, none,
          .ct1Received e a sk ct1 enc.nextChunk.2⟩
  /-- Nothing to send while waiting for `ct₂`. -/
  | idleEkSent (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym) :
      SendEdge (.ekSentCt1Received e a sk ct1 dec)
        ⟨⟨e, .none, none⟩, e - 1, none, .ekSentCt1Received e a sk ct1 dec⟩
  /-- Nothing to send while waiting for the header. -/
  | idleNoHeader (e : ℕ) (a : AuthState) (dec : DecoderState (P.inc.PKheader × P.Mac) P.Sym) :
      SendEdge (.noHeaderReceived e a dec)
        ⟨⟨e, .none, none⟩, e - 1, none, .noHeaderReceived e a dec⟩
  /-- Edge 7: encapsulate against the received header, output the epoch key, update the
  authenticator, and emit the first `ct₁` chunk. -/
  | encaps1 (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (dec : DecoderState P.inc.PKvector P.Sym)
      (es : P.inc.St) (ct1 : P.inc.C₁) (k : P.K)
      (h : (es, ct1, k) ∈ support (P.inc.encaps1 hdr)) :
      SendEdge (.headerReceived e a hdr dec)
        ⟨⟨e, .ct1, some (EncoderState.init P.ecpCt1 ct1).nextChunk.1⟩, e - 1,
          some (e, P.kdfOK k e),
          .ct1Sampled e (auth.update a e (P.kdfOK k e)) hdr es ct1
            (EncoderState.init P.ecpCt1 ct1).nextChunk.2 dec⟩
  /-- Emit the next `ct₁` chunk while decoding the vector. -/
  | ct1Chunk (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St) (ct1 : P.inc.C₁)
      (enc : EncoderState P.inc.C₁ P.Sym) (dec : DecoderState P.inc.PKvector P.Sym) :
      SendEdge (.ct1Sampled e a hdr es ct1 enc dec)
        ⟨⟨e, .ct1, some enc.nextChunk.1⟩, e - 1, none,
          .ct1Sampled e a hdr es ct1 enc.nextChunk.2 dec⟩
  /-- Emit the next `ct₁` chunk after the vector is complete. -/
  | ct1ChunkVec (e : ℕ) (a : AuthState) (es : P.inc.St) (ct1 : P.inc.C₁) (hdr : P.inc.PKheader)
      (vec : P.inc.PKvector) (enc : EncoderState P.inc.C₁ P.Sym) :
      SendEdge (.ekReceivedCt1Sampled e a es ct1 hdr vec enc)
        ⟨⟨e, .ct1, some enc.nextChunk.1⟩, e - 1, none,
          .ekReceivedCt1Sampled e a es ct1 hdr vec enc.nextChunk.2⟩
  /-- Nothing to send while waiting for the vector after the acknowledgement. -/
  | idleAcknowledged (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St)
      (ct1 : P.inc.C₁) (dec : DecoderState P.inc.PKvector P.Sym) :
      SendEdge (.ct1Acknowledged e a hdr es ct1 dec)
        ⟨⟨e, .none, none⟩, e - 1, none, .ct1Acknowledged e a hdr es ct1 dec⟩
  /-- Emit the next `ct₂` chunk. -/
  | ct2Chunk (e : ℕ) (a : AuthState) (enc : EncoderState (P.inc.C₂ × P.Mac) P.Sym) :
      SendEdge (.ct2Sampled e a enc)
        ⟨⟨e, .ct2, some enc.nextChunk.1⟩, e - 1, none, .ct2Sampled e a enc.nextChunk.2⟩

/-- `send` from `keysUnsampled` maps the sampled key pair to its result (edge 1). -/
theorem send_keysUnsampled_eq (e : ℕ) (a : AuthState) :
    send P auth (.keysUnsampled e a) =
      (fun kp : P.PK × P.SK =>
        (⟨⟨e, .hdr, some (EncoderState.init P.ecpHdr
            (P.inc.toHeader kp.1, auth.macHeader a e (P.inc.toHeader kp.1))).nextChunk.1⟩,
          e - 1, none,
          .keysSampled e a kp.2 (P.inc.toVector kp.1) (EncoderState.init P.ecpHdr
            (P.inc.toHeader kp.1, auth.macHeader a e (P.inc.toHeader kp.1))).nextChunk.2⟩ :
          SendResult P AuthState)) <$> P.kem.keygen := by
  simp only [send, map_eq_bind_pure_comp]
  exact bind_congr fun kp => by cases kp; rfl

/-- `send` from `headerReceived` maps the sampled encapsulation to its result (edge 7). -/
theorem send_headerReceived_eq (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader)
    (dec : DecoderState P.inc.PKvector P.Sym) :
    send P auth (.headerReceived e a hdr dec) =
      (fun c : P.inc.St × P.inc.C₁ × P.K =>
        (⟨⟨e, .ct1, some (EncoderState.init P.ecpCt1 c.2.1).nextChunk.1⟩, e - 1,
          some (e, P.kdfOK c.2.2 e),
          .ct1Sampled e (auth.update a e (P.kdfOK c.2.2 e)) hdr c.1 c.2.1
            (EncoderState.init P.ecpCt1 c.2.1).nextChunk.2 dec⟩ : SendResult P AuthState)) <$>
        P.inc.encaps1 hdr := by
  simp only [send, map_eq_bind_pure_comp]
  exact bind_congr fun c => by obtain ⟨es, ct1, k⟩ := c; rfl

/-- The results of `send` from `st` are exactly the send edges from `st`. -/
theorem mem_support_send_iff {st : State P AuthState} {r : SendResult P AuthState} :
    r ∈ support (send P auth st) ↔ SendEdge auth st r := by
  constructor
  · intro hr
    cases st
    case keysUnsampled e a =>
      simp only [send, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨⟨pk, sk⟩, h, rfl⟩ := hr
      exact .keygen e a pk sk h
    case headerReceived e a hdr dec =>
      simp only [send, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨⟨es, ct1, k⟩, h, rfl⟩ := hr
      exact .encaps1 e a hdr dec es ct1 k h
    all_goals
      simp only [send, mem_support_pure_iff] at hr
      subst hr
      constructor
  · intro h
    cases h
    case keygen e a pk sk h =>
      simp only [send, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨(pk, sk), h, rfl⟩
    case encaps1 e a hdr dec es ct1 k h =>
      simp only [send, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨(es, ct1, k), h, rfl⟩
    all_goals simp [send]

namespace SendEdge

variable {auth} {st : State P AuthState} {r : SendResult P AuthState}

/-- A send keeps the epoch and stamps it on the message. -/
theorem epoch_eq (h : SendEdge auth st r) : r.state.epoch = st.epoch ∧ r.msg.epoch = st.epoch := by
  cases h <;> simp [State.epoch]

/-- A send reports the epoch before the current one. -/
theorem sendingEpoch_eq (h : SendEdge auth st r) : r.sendingEpoch = st.epoch - 1 := by
  cases h <;> rfl

/-- The sent message is well formed. -/
theorem wellFormed (h : SendEdge auth st r) : r.msg.wellFormed = true := by
  cases h <;> rfl

/-- A send keeps the role and does not move the step backwards. -/
theorem controlPosition (h : SendEdge auth st r) :
    r.state.controlPosition.isGenerator = st.controlPosition.isGenerator ∧
      st.controlPosition.step ≤ r.state.controlPosition.step := by
  cases h <;> simp [State.controlPosition]

/-- Only an encapsulator with the completed epoch sends `ct₂`. -/
theorem completedEpoch_of_ct2 (h : SendEdge auth st r) (hty : r.msg.type = .ct2) :
    r.msg.epoch ≤ st.completedEpoch := by
  cases h <;> simp_all [State.completedEpoch]

/-- A send without output key keeps the completed epoch. A send with output key `(tI, _)`
completes epoch `tI`, the epoch after the previously completed one. -/
theorem completedEpoch (h : SendEdge auth st r) (hpos : 0 < st.epoch) :
    match r.outputKey with
    | none => r.state.completedEpoch = st.completedEpoch
    | some (tI, _) => tI = st.completedEpoch + 1 ∧ r.state.completedEpoch = tI := by
  cases h
  all_goals simp only [State.completedEpoch, State.epoch, and_true] at hpos ⊢
  all_goals omega

/-- A send does not lower the completed epoch. -/
theorem completedEpoch_mono (h : SendEdge auth st r) (hpos : 0 < st.epoch) :
    st.completedEpoch ≤ r.state.completedEpoch := by
  have := h.completedEpoch hpos
  cases hk : r.outputKey <;> simp only [hk] at this <;> omega

/-- A send outputs a key only from `headerReceived`. -/
theorem outputKey_eq_none (h : SendEdge auth st r)
    (hst : ∀ e a hdr dec, st ≠ .headerReceived e a hdr dec) : r.outputKey = none := by
  cases h <;> first | rfl | exact absurd rfl (hst _ _ _ _)

end SendEdge

/-! ### Receive edges -/

variable [DecidableEq P.Sym]

/-- The transitions of `receive` that accept a message. `ignore` leaves the state unchanged and
reports the previous epoch; the other constructors are the edges of Figure 1, with the chunk
bookkeeping of `receive`. -/
inductive ReceiveEdge : State P AuthState → Message P.Sym → RecvResult P AuthState → Prop
  /-- An ill-formed, off-epoch or unexpected message leaves the state unchanged. -/
  | ignore (st : State P AuthState) (msg : Message P.Sym) :
      ReceiveEdge st msg ⟨st.epoch - 1, none, st⟩
  /-- Edge 2: the first `ct₁` chunk reaches the key generator, which starts the vector stream. -/
  | ct1First (e : ℕ) (a : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
      (enc : EncoderState (P.inc.PKheader × P.Mac) P.Sym) (chunk : ℕ × P.Sym) :
      ReceiveEdge (.keysSampled e a sk vec enc) ⟨e, .ct1, some chunk⟩
        ⟨e - 1, none, .headerSent e a sk ((DecoderState.empty P.ecpCt1).addChunk chunk)
          (EncoderState.init P.ecpEk vec)⟩
  /-- A `ct₁` chunk that does not complete `ct₁`. -/
  | ct1Chunk (e : ℕ) (a : AuthState) (sk : P.SK) (dec : DecoderState P.inc.C₁ P.Sym)
      (enc : EncoderState P.inc.PKvector P.Sym) (chunk : ℕ × P.Sym)
      (h : (dec.addChunk chunk).decodedPayload = none) :
      ReceiveEdge (.headerSent e a sk dec enc) ⟨e, .ct1, some chunk⟩
        ⟨e - 1, none, .headerSent e a sk (dec.addChunk chunk) enc⟩
  /-- Edge 3: the `ct₁` chunk that completes `ct₁`. -/
  | ct1Done (e : ℕ) (a : AuthState) (sk : P.SK) (dec : DecoderState P.inc.C₁ P.Sym)
      (enc : EncoderState P.inc.PKvector P.Sym) (chunk : ℕ × P.Sym) (ct1 : P.inc.C₁)
      (h : (dec.addChunk chunk).decodedPayload = some ct1) :
      ReceiveEdge (.headerSent e a sk dec enc) ⟨e, .ct1, some chunk⟩
        ⟨e - 1, none, .ct1Received e a sk ct1 enc⟩
  /-- Edge 4: the first `ct₂` chunk reaches the key generator. -/
  | ct2First (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (enc : EncoderState P.inc.PKvector P.Sym) (chunk : ℕ × P.Sym) :
      ReceiveEdge (.ct1Received e a sk ct1 enc) ⟨e, .ct2, some chunk⟩
        ⟨e - 1, none, .ekSentCt1Received e a sk ct1 ((DecoderState.empty P.ecpCt2).addChunk chunk)⟩
  /-- A `ct₂` chunk that does not complete `ct₂`. -/
  | ct2Chunk (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym) (chunk : ℕ × P.Sym)
      (h : (dec.addChunk chunk).decodedPayload = none) :
      ReceiveEdge (.ekSentCt1Received e a sk ct1 dec) ⟨e, .ct2, some chunk⟩
        ⟨e - 1, none, .ekSentCt1Received e a sk ct1 (dec.addChunk chunk)⟩
  /-- Edge 5: `ct₂` completes, decapsulation returns `k`, and the ciphertext tag verifies under
  the authenticator updated with the epoch key `kdfOK k e`. The party outputs that key and
  advances to epoch `e + 1`. -/
  | ct2Done (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym) (chunk : ℕ × P.Sym) (ct2 : P.inc.C₂)
      (tag : P.Mac) (k : P.K)
      (hdec : (dec.addChunk chunk).decodedPayload = some (ct2, tag))
      (hk : P.hDet.decapsDet sk (P.inc.splitC.symm (ct1, ct2)) = some k)
      (htag : auth.verifyCiphertext (auth.update a e (P.kdfOK k e)) e (ct1, ct2) tag = true) :
      ReceiveEdge (.ekSentCt1Received e a sk ct1 dec) ⟨e, .ct2, some chunk⟩
        ⟨e - 1, some (e, P.kdfOK k e),
          .noHeaderReceived (e + 1) (auth.update a e (P.kdfOK k e)) (DecoderState.empty P.ecpHdr)⟩
  /-- A header chunk that does not complete the header. -/
  | hdrChunk (e : ℕ) (a : AuthState) (dec : DecoderState (P.inc.PKheader × P.Mac) P.Sym)
      (chunk : ℕ × P.Sym) (h : (dec.addChunk chunk).decodedPayload = none) :
      ReceiveEdge (.noHeaderReceived e a dec) ⟨e, .hdr, some chunk⟩
        ⟨e - 1, none, .noHeaderReceived e a (dec.addChunk chunk)⟩
  /-- Edge 6: the header completes and its tag verifies. -/
  | hdrDone (e : ℕ) (a : AuthState) (dec : DecoderState (P.inc.PKheader × P.Mac) P.Sym)
      (chunk : ℕ × P.Sym) (hdr : P.inc.PKheader) (tag : P.Mac)
      (hdec : (dec.addChunk chunk).decodedPayload = some (hdr, tag))
      (htag : auth.verifyHeader a e hdr tag = true) :
      ReceiveEdge (.noHeaderReceived e a dec) ⟨e, .hdr, some chunk⟩
        ⟨e - 1, none, .headerReceived e a hdr (DecoderState.empty P.ecpEk)⟩
  /-- A vector chunk that does not complete the vector. -/
  | ekChunk (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St) (ct1 : P.inc.C₁)
      (enc : EncoderState P.inc.C₁ P.Sym) (dec : DecoderState P.inc.PKvector P.Sym)
      (chunk : ℕ × P.Sym) (h : (dec.addChunk chunk).decodedPayload = none) :
      ReceiveEdge (.ct1Sampled e a hdr es ct1 enc dec) ⟨e, .ek, some chunk⟩
        ⟨e - 1, none, .ct1Sampled e a hdr es ct1 enc (dec.addChunk chunk)⟩
  /-- Edge 10: the vector completes before any acknowledgement and passes `validPK`. -/
  | ekDone (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St) (ct1 : P.inc.C₁)
      (enc : EncoderState P.inc.C₁ P.Sym) (dec : DecoderState P.inc.PKvector P.Sym)
      (chunk : ℕ × P.Sym) (vec : P.inc.PKvector)
      (hdec : (dec.addChunk chunk).decodedPayload = some vec)
      (hvalid : P.inc.validPK hdr vec = true) :
      ReceiveEdge (.ct1Sampled e a hdr es ct1 enc dec) ⟨e, .ek, some chunk⟩
        ⟨e - 1, none, .ekReceivedCt1Sampled e a es ct1 hdr vec enc⟩
  /-- Edge 8: an acknowledgement chunk arrives before the vector is complete. -/
  | ackEarly (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St) (ct1 : P.inc.C₁)
      (enc : EncoderState P.inc.C₁ P.Sym) (dec : DecoderState P.inc.PKvector P.Sym)
      (chunk : ℕ × P.Sym) (h : (dec.addChunk chunk).decodedPayload = none) :
      ReceiveEdge (.ct1Sampled e a hdr es ct1 enc dec) ⟨e, .ekCt1Ack, some chunk⟩
        ⟨e - 1, none, .ct1Acknowledged e a hdr es ct1 (dec.addChunk chunk)⟩
  /-- Edge 9: an acknowledgement chunk completes the vector; `encaps2` runs and the tagged `ct₂`
  stream starts. -/
  | ackDone (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St) (ct1 : P.inc.C₁)
      (enc : EncoderState P.inc.C₁ P.Sym) (dec : DecoderState P.inc.PKvector P.Sym)
      (chunk : ℕ × P.Sym) (vec : P.inc.PKvector)
      (hdec : (dec.addChunk chunk).decodedPayload = some vec)
      (hvalid : P.inc.validPK hdr vec = true) :
      ReceiveEdge (.ct1Sampled e a hdr es ct1 enc dec) ⟨e, .ekCt1Ack, some chunk⟩
        ⟨e - 1, none, .ct2Sampled e a (EncoderState.init P.ecpCt2
          (P.hEnc2.encaps2Det es hdr vec,
            auth.macCiphertext a e (ct1, P.hEnc2.encaps2Det es hdr vec)))⟩
  /-- Edge 12: an acknowledgement arrives after the vector is complete; its chunk is discarded. -/
  | ackLate (e : ℕ) (a : AuthState) (es : P.inc.St) (ct1 : P.inc.C₁) (hdr : P.inc.PKheader)
      (vec : P.inc.PKvector) (enc : EncoderState P.inc.C₁ P.Sym) (chunk : ℕ × P.Sym) :
      ReceiveEdge (.ekReceivedCt1Sampled e a es ct1 hdr vec enc) ⟨e, .ekCt1Ack, some chunk⟩
        ⟨e - 1, none, .ct2Sampled e a (EncoderState.init P.ecpCt2
          (P.hEnc2.encaps2Det es hdr vec,
            auth.macCiphertext a e (ct1, P.hEnc2.encaps2Det es hdr vec)))⟩
  /-- An acknowledgement chunk after the acknowledgement that does not complete the vector. -/
  | ackChunk (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St) (ct1 : P.inc.C₁)
      (dec : DecoderState P.inc.PKvector P.Sym) (chunk : ℕ × P.Sym)
      (h : (dec.addChunk chunk).decodedPayload = none) :
      ReceiveEdge (.ct1Acknowledged e a hdr es ct1 dec) ⟨e, .ekCt1Ack, some chunk⟩
        ⟨e - 1, none, .ct1Acknowledged e a hdr es ct1 (dec.addChunk chunk)⟩
  /-- Edge 11: the vector completes after the acknowledgement. -/
  | ackVecDone (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader) (es : P.inc.St) (ct1 : P.inc.C₁)
      (dec : DecoderState P.inc.PKvector P.Sym) (chunk : ℕ × P.Sym) (vec : P.inc.PKvector)
      (hdec : (dec.addChunk chunk).decodedPayload = some vec)
      (hvalid : P.inc.validPK hdr vec = true) :
      ReceiveEdge (.ct1Acknowledged e a hdr es ct1 dec) ⟨e, .ekCt1Ack, some chunk⟩
        ⟨e - 1, none, .ct2Sampled e a (EncoderState.init P.ecpCt2
          (P.hEnc2.encaps2Det es hdr vec,
            auth.macCiphertext a e (ct1, P.hEnc2.encaps2Det es hdr vec)))⟩
  /-- Edge 13: a message of the next epoch moves the encapsulator to the next epoch, where it
  generates the keys. The transition reports the finished epoch. -/
  | nextEpoch (e : ℕ) (a : AuthState) (enc : EncoderState (P.inc.C₂ × P.Mac) P.Sym)
      (msg : Message P.Sym) (hep : msg.epoch = e + 1) :
      ReceiveEdge (.ct2Sampled e a enc) msg ⟨e, none, .keysUnsampled (e + 1) a⟩

/-- In `hr : receive P auth st ⟨me, mt, md⟩ = .ok r` with `st` a constructor, unfold `receive`,
split its guards, substitute `r`, and identify `me` with the epoch that a guard compared it to. -/
local macro "receive_cases" hr:ident : tactic =>
  `(tactic| (simp only [receive] at $hr:ident
             repeat' split at $hr:ident
             all_goals cases $hr:ident
             all_goals subst_vars))

/-- A well-formed message of the next epoch moves `ct2Sampled` to `keysUnsampled` (edge 13). -/
theorem receive_ct2Sampled_of_epoch_succ {e : ℕ} {a : AuthState}
    {enc : EncoderState (P.inc.C₂ × P.Mac) P.Sym} {msg : Message P.Sym}
    (hwf : msg.wellFormed = true) (hep : msg.epoch = e + 1) :
    receive P auth (.ct2Sampled e a enc) msg = .ok ⟨e, none, .keysUnsampled (e + 1) a⟩ := by
  simp [receive, hwf, hep]

/-- Every accepting result of `receive` is a receive edge. -/
theorem ReceiveEdge.of_eq_ok {st : State P AuthState} {msg : Message P.Sym}
    {r : RecvResult P AuthState} (hr : receive P auth st msg = .ok r) :
    ReceiveEdge auth st msg r := by
  -- In each state, name the edge taken. `ignore` is tried last: unifying it against another
  -- edge compares a decoder with its extension by a chunk, which unfolds `addChunk` and its
  -- decidability instance.
  obtain ⟨me, mt, md⟩ := msg
  cases st
  case keysUnsampled => receive_cases hr; all_goals exact .ignore _ _
  case keysSampled =>
    receive_cases hr
    all_goals first | exact .ct1First _ _ _ _ _ _ | exact .ignore _ _
  case headerSent =>
    receive_cases hr
    all_goals first
      | exact .ct1Chunk _ _ _ _ _ _ ‹_›
      | exact .ct1Done _ _ _ _ _ _ _ ‹_›
      | exact .ignore _ _
  case ct1Received =>
    receive_cases hr
    all_goals first | exact .ct2First _ _ _ _ _ _ | exact .ignore _ _
  case ekSentCt1Received =>
    receive_cases hr
    all_goals first
      | exact .ct2Chunk _ _ _ _ _ _ ‹_›
      | exact .ct2Done _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›
      | exact .ignore _ _
  case noHeaderReceived =>
    receive_cases hr
    all_goals first
      | exact .hdrChunk _ _ _ _ ‹_›
      | exact .hdrDone _ _ _ _ _ _ ‹_› ‹_›
      | exact .ignore _ _
  case headerReceived => receive_cases hr; all_goals exact .ignore _ _
  case ct1Sampled =>
    receive_cases hr
    all_goals first
      | exact .ekChunk _ _ _ _ _ _ _ _ ‹_›
      | exact .ekDone _ _ _ _ _ _ _ _ _ ‹_› ‹_›
      | exact .ackEarly _ _ _ _ _ _ _ _ ‹_›
      | exact .ackDone _ _ _ _ _ _ _ _ _ ‹_› ‹_›
      | exact .ignore _ _
  case ekReceivedCt1Sampled =>
    receive_cases hr
    all_goals first | exact .ackLate _ _ _ _ _ _ _ _ | exact .ignore _ _
  case ct1Acknowledged =>
    receive_cases hr
    all_goals first
      | exact .ackChunk _ _ _ _ _ _ _ ‹_›
      | exact .ackVecDone _ _ _ _ _ _ _ _ ‹_› ‹_›
      | exact .ignore _ _
  case ct2Sampled =>
    receive_cases hr
    all_goals first | exact .nextEpoch _ _ _ _ rfl | exact .ignore _ _

namespace ReceiveEdge

variable {auth} {st : State P AuthState} {msg : Message P.Sym} {r : RecvResult P AuthState}

/-- A receive does not lower the epoch and raises it by at most one. -/
theorem epoch_le (h : ReceiveEdge auth st msg r) :
    st.epoch ≤ r.state.epoch ∧ r.state.epoch ≤ st.epoch + 1 := by
  cases h
  case ignore => exact ⟨le_rfl, Nat.le_succ _⟩
  all_goals simp only [State.epoch]; omega

/-- A receive that outputs a key or changes the epoch is an epoch advance. -/
theorem epoch_eq_or_succ (h : ReceiveEdge auth st msg r) :
    (r.outputKey = none ∧ r.state.epoch = st.epoch) ∨ r.state.epoch = st.epoch + 1 := by
  cases h <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl

/-- A receive that advances the epoch is edge 13, moving an encapsulator to `keysUnsampled` on a
message of the next epoch, or edge 5, moving a key generator to `noHeaderReceived` on a `ct₂`
message of its epoch. -/
theorem advance (h : ReceiveEdge auth st msg r) (hne : r.state.epoch ≠ st.epoch) :
    (st.controlPosition.isGenerator = false ∧ msg.epoch = st.epoch + 1 ∧
        ∃ a, r.state = .keysUnsampled (st.epoch + 1) a) ∨
      (st.controlPosition.isGenerator = true ∧ msg.type = .ct2 ∧ msg.epoch = st.epoch ∧
        ∃ a dec, r.state = .noHeaderReceived (st.epoch + 1) a dec) := by
  cases h <;> first
    | exact absurd rfl hne
    | exact Or.inl ⟨rfl, ‹_›, _, rfl⟩
    | exact Or.inr ⟨rfl, rfl, rfl, _, _, rfl⟩

/-- A receive without output key keeps the completed epoch. A receive with output key `(tI, _)`
completes epoch `tI`, the epoch after the previously completed one. -/
theorem completedEpoch (h : ReceiveEdge auth st msg r) (hpos : 0 < st.epoch) :
    0 < r.state.epoch ∧
      match r.outputKey with
      | none => r.state.completedEpoch = st.completedEpoch
      | some (tI, _) => tI = st.completedEpoch + 1 ∧ r.state.completedEpoch = tI := by
  cases h
  case ignore => exact ⟨hpos, rfl⟩
  all_goals simp only [State.completedEpoch, State.epoch, and_true] at hpos ⊢
  all_goals omega

/-- A receive does not lower the completed epoch. -/
theorem completedEpoch_mono (h : ReceiveEdge auth st msg r) (hpos : 0 < st.epoch) :
    st.completedEpoch ≤ r.state.completedEpoch := by
  have := (h.completedEpoch hpos).2
  cases hk : r.outputKey <;> simp only [hk] at this <;> omega

/-- If the state and the message are at most one epoch past `c`, and a `ct₂` message at most at
`c`, the receive leaves the epoch at most one past `c`. -/
theorem epoch_le_of_le (h : ReceiveEdge auth st msg r) (c : ℕ) (hst : st.epoch ≤ c + 1)
    (hmsg : msg.epoch ≤ c + 1) (hct2 : msg.type = .ct2 → msg.epoch ≤ c) :
    r.state.epoch ≤ c + 1 := by
  cases h
  case ignore => exact hst
  all_goals simp only [State.epoch] at hst hmsg hct2 ⊢
  all_goals first | omega | (have := hct2 trivial; omega)

/-- A receive within the same epoch keeps the role and does not move the step backwards. -/
theorem controlPosition_of_epoch_eq (h : ReceiveEdge auth st msg r)
    (heq : r.state.epoch = st.epoch) :
    r.state.controlPosition.isGenerator = st.controlPosition.isGenerator ∧
      st.controlPosition.step ≤ r.state.controlPosition.step := by
  cases h
  case ignore => exact ⟨rfl, le_rfl⟩
  all_goals simp [State.controlPosition, State.epoch] at heq ⊢

/-- A receive outputs a key only when it completes `ct₂`. -/
theorem outputKey_eq_none (h : ReceiveEdge auth st msg r)
    (hst : ∀ e a sk ct1 dec, st ≠ .ekSentCt1Received e a sk ct1 dec) : r.outputKey = none := by
  cases h <;> first | rfl | exact absurd rfl (hst _ _ _ _ _)

end ReceiveEdge

end MLKEMBraid
