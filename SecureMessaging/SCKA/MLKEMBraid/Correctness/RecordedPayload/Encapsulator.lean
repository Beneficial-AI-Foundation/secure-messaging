/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.RecordedPayload.Generator

/-!
# Recorded messages received by an encapsulator

For each encapsulating state, conditions under which receiving a message recorded by the peer
succeeds, outputs no key, and preserves `LocalPayloadInv`.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable {P : Parameters ProbComp} [DecidableEq P.Sym] {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
  (ik : InitKey) (T : ℕ → EpochTranscript P)

/-- Receiving a recorded message in `noHeaderReceived` succeeds without key output and preserves
`LocalPayloadInv`. -/
theorem receive_noHeaderReceived_payload (hHdrCorrect : P.ecpHdr.ec.Correct)
    (e : ℕ) (a : AuthState) (dec : DecoderState (P.inc.PKheader × P.Mac) P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.noHeaderReceived e a dec))
    (hPayload : MessagePayloadInv auth ik T msg)
    (hNoEncaps : (T e).encaps1 = none) :
    ∃ r, receive P auth (.noHeaderReceived e a dec) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
  -- Only an epoch-`e` header chunk changes the state; a complete header carries the tag of
  -- the transcript authenticator, so it verifies.
  rcases msg with ⟨me, mt, md⟩
  cases mt with
  | hdr =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some chunk =>
          by_cases he : me = e
          · subst me
            simp only [MessagePayloadInv] at hPayload
            obtain ⟨pk, sk, i, hkp, hchunk⟩ := hPayload
            obtain ⟨ha, hdec⟩ := hLocal
            rw [hkp] at hdec
            have hch := Option.some.inj hchunk
            have hC :=
              DecoderState.addChunk_encode_of_payloadChunks P.ecpHdr hHdrCorrect _ dec hdec i
            rw [← hch] at hC
            obtain ⟨hecp, ⟨I, hchunks⟩, hnone | hsome⟩ := hC
            · refine ⟨⟨e - 1, none, .noHeaderReceived e a (dec.addChunk chunk)⟩,
                by simp [receive, Message.wellFormed, hnone], rfl, ha, ?_⟩
              rw [hkp]
              exact ⟨hecp, I, hchunks⟩
            · refine ⟨⟨e - 1, none, .headerReceived e a (P.inc.toHeader pk)
                (DecoderState.empty P.ecpEk)⟩, ?_, rfl, ha, hNoEncaps, pk, sk, hkp, rfl, rfl⟩
              simp [receive, Message.wellFormed, hsome, ha, auth.verifyHeader_correct]
          · exact ⟨⟨e - 1, none, .noHeaderReceived e a dec⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

/-- Receiving a recorded message in `ct1Sampled` succeeds without key output and preserves
`LocalPayloadInv`. -/
theorem receive_ct1Sampled_payload (hEkCorrect : P.ecpEk.ec.Correct)
    (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader)
    (encapsState : P.inc.St) (ct1 : P.inc.C₁)
    (enc : EncoderState P.inc.C₁ P.Sym)
    (dec : DecoderState P.inc.PKvector P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.ct1Sampled e a hdr encapsState ct1 enc dec))
    (hPayload : MessagePayloadInv auth ik T msg) :
    ∃ r, receive P auth (.ct1Sampled e a hdr encapsState ct1 enc dec) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
  -- A recorded vector chunk extends the decoder of the transcript key's vector; a complete
  -- vector passes `validPK` against its own header.
  have hvalid : ∀ pk, P.inc.validPK (P.inc.toHeader pk) (P.inc.toVector pk) = true :=
    fun pk => (P.inc.splitPK pk).2
  rcases msg with ⟨me, mt, md⟩
  cases mt with
  | ek =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some chunk =>
          by_cases he : me = e
          · subst me
            simp only [MessagePayloadInv] at hPayload
            obtain ⟨pk', sk', i, hkp', hchunk⟩ := hPayload
            obtain ⟨ha, pk, sk, key, hkp, hc, hhdr, henc, hdec⟩ := hLocal
            obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
            subst hhdr
            have hch := Option.some.inj hchunk
            have hC := DecoderState.addChunk_encode_of_payloadChunks P.ecpEk hEkCorrect _ dec hdec i
            rw [← hch] at hC
            obtain ⟨hecp, ⟨I, hchunks⟩, hnone | hsome⟩ := hC
            · exact ⟨⟨e - 1, none, .ct1Sampled e a (P.inc.toHeader pk) encapsState ct1 enc
                  (dec.addChunk chunk)⟩, by simp [receive, Message.wellFormed, hnone], rfl,
                ha, pk, sk, key, hkp, hc, rfl, henc, hecp, I, hchunks⟩
            · exact ⟨⟨e - 1, none, .ekReceivedCt1Sampled e a encapsState ct1
                  (P.inc.toHeader pk) (P.inc.toVector pk) enc⟩,
                by simp [receive, Message.wellFormed, hsome, hvalid], rfl,
                ha, pk, sk, key, hkp, hc, rfl, rfl, henc⟩
          · exact ⟨⟨e - 1, none, .ct1Sampled e a hdr encapsState ct1 enc dec⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | ekCt1Ack =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some chunk =>
          by_cases he : me = e
          · subst me
            simp only [MessagePayloadInv] at hPayload
            obtain ⟨pk', sk', i, hkp', hchunk⟩ := hPayload
            obtain ⟨ha, pk, sk, key, hkp, hc, hhdr, -, hdec⟩ := hLocal
            obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
            subst hhdr ha
            have hch := Option.some.inj hchunk
            have hC := DecoderState.addChunk_encode_of_payloadChunks P.ecpEk hEkCorrect _ dec hdec i
            rw [← hch] at hC
            obtain ⟨hecp, ⟨I, hchunks⟩, hnone | hsome⟩ := hC
            · exact ⟨⟨e - 1, none, .ct1Acknowledged e (transcriptAuth auth ik T e)
                  (P.inc.toHeader pk) encapsState ct1 (dec.addChunk chunk)⟩,
                by simp [receive, Message.wellFormed, hnone], rfl,
                rfl, pk, sk, key, hkp, hc, rfl, hecp, I, hchunks⟩
            · exact ⟨⟨e - 1, none, .ct2Sampled e (transcriptAuth auth ik T e)
                  (EncoderState.init P.ecpCt2
                    (P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk),
                      auth.macCiphertext (transcriptAuth auth ik T e) e
                        (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk)
                          (P.inc.toVector pk))))⟩,
                by simp [receive, Message.wellFormed, hsome, hvalid], rfl,
                rfl, pk, sk, encapsState, ct1, key, hkp, hc, rfl, rfl⟩
          · exact ⟨⟨e - 1, none, .ct1Sampled e a hdr encapsState ct1 enc dec⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

/-- Receiving any message in `ekReceivedCt1Sampled` succeeds without key output and preserves
`LocalPayloadInv`. -/
theorem receive_ekReceivedCt1Sampled_payload
    (e : ℕ) (a : AuthState) (encapsState : P.inc.St)
    (ct1 : P.inc.C₁) (hdr : P.inc.PKheader) (vec : P.inc.PKvector)
    (enc : EncoderState P.inc.C₁ P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc)) :
    ∃ r, receive P auth (.ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
  -- The stored header and vector belong to the transcript key, so the new `ct₂` encoder
  -- carries the ciphertext tag of the transcript authenticator.
  rcases msg with ⟨me, mt, md⟩
  cases mt with
  | ekCt1Ack =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some x =>
          by_cases he : me = e
          · subst me
            obtain ⟨ha, pk, sk, key, hkp, hc, hhdr, hvec, -⟩ := hLocal
            subst ha hhdr hvec
            exact ⟨⟨e - 1, none, .ct2Sampled e (transcriptAuth auth ik T e)
                (EncoderState.init P.ecpCt2
                  (P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk),
                    auth.macCiphertext (transcriptAuth auth ik T e) e
                      (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk)
                        (P.inc.toVector pk))))⟩,
              by simp [receive, Message.wellFormed], rfl,
              rfl, pk, sk, encapsState, ct1, key, hkp, hc, rfl, rfl⟩
          · exact ⟨⟨e - 1, none, .ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

/-- Receiving a recorded message in `ct1Acknowledged` succeeds without key output and preserves
`LocalPayloadInv`. -/
theorem receive_ct1Acknowledged_payload (hEkCorrect : P.ecpEk.ec.Correct)
    (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader)
    (encapsState : P.inc.St) (ct1 : P.inc.C₁)
    (dec : DecoderState P.inc.PKvector P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.ct1Acknowledged e a hdr encapsState ct1 dec))
    (hPayload : MessagePayloadInv auth ik T msg) :
    ∃ r, receive P auth (.ct1Acknowledged e a hdr encapsState ct1 dec) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
  -- A recorded `ekCt1Ack` chunk extends the vector decoder; completing the vector runs `Encaps2`
  -- on the transcript key and tags `ct₂` with the transcript authenticator.
  have hvalid : ∀ pk, P.inc.validPK (P.inc.toHeader pk) (P.inc.toVector pk) = true :=
    fun pk => (P.inc.splitPK pk).2
  rcases msg with ⟨me, mt, md⟩
  cases mt with
  | ekCt1Ack =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some chunk =>
          by_cases he : me = e
          · subst me
            simp only [MessagePayloadInv] at hPayload
            obtain ⟨pk', sk', i, hkp', hchunk⟩ := hPayload
            obtain ⟨ha, pk, sk, key, hkp, hc, hhdr, hdec⟩ := hLocal
            obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
            subst hhdr ha
            have hch := Option.some.inj hchunk
            have hC := DecoderState.addChunk_encode_of_payloadChunks P.ecpEk hEkCorrect _ dec hdec i
            rw [← hch] at hC
            obtain ⟨hecp, ⟨I, hchunks⟩, hnone | hsome⟩ := hC
            · exact ⟨⟨e - 1, none, .ct1Acknowledged e (transcriptAuth auth ik T e)
                  (P.inc.toHeader pk) encapsState ct1 (dec.addChunk chunk)⟩,
                by simp [receive, Message.wellFormed, hnone], rfl,
                rfl, pk, sk, key, hkp, hc, rfl, hecp, I, hchunks⟩
            · exact ⟨⟨e - 1, none, .ct2Sampled e (transcriptAuth auth ik T e)
                  (EncoderState.init P.ecpCt2
                    (P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk),
                      auth.macCiphertext (transcriptAuth auth ik T e) e
                        (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk)
                          (P.inc.toVector pk))))⟩,
                by simp [receive, Message.wellFormed, hsome, hvalid], rfl,
                rfl, pk, sk, encapsState, ct1, key, hkp, hc, rfl, rfl⟩
          · exact ⟨⟨e - 1, none, .ct1Acknowledged e a hdr encapsState ct1 dec⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

/-- With no next-epoch samples recorded, `ct2Sampled` accepts any message without key output and
preserves `LocalPayloadInv`. -/
theorem receive_ct2Sampled_payload
    (e : ℕ) (a : AuthState) (enc : EncoderState (P.inc.C₂ × P.Mac) P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.ct2Sampled e a enc))
    (hNext : (T (e + 1)).keypair = none ∧ (T (e + 1)).encaps1 = none) :
    ∃ r, receive P auth (.ct2Sampled e a enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
  -- Moving to `keysUnsampled (e + 1)` keeps the authenticator of epoch `e`.
  cases hwf : msg.wellFormed with
  | false =>
      exact ⟨⟨e - 1, none, .ct2Sampled e a enc⟩, by simp [receive, hwf, State.epoch], rfl,
        hLocal⟩
  | true =>
      by_cases he : msg.epoch = e + 1
      · refine ⟨⟨e, none, .keysUnsampled (e + 1) a⟩, by simp [receive, hwf, he], rfl, ?_,
          hNext.1, hNext.2⟩
        rw [Nat.add_sub_cancel]
        exact hLocal.1
      · exact ⟨⟨e - 1, none, .ct2Sampled e a enc⟩,
          by simp [receive, hwf, he, State.epoch], rfl, hLocal⟩

end MLKEMBraid
