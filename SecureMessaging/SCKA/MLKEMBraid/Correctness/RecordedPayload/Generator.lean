/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant

/-!
# Recorded messages received by a key generator

A successful receive of a recorded message by a key generator keeps `LocalPayloadInv` when any
output key agrees with the peer's recorded key for that epoch. Only `ekSentCt1Received` outputs a
key: the epoch key decapsulated from the recorded ciphertext.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

namespace Correctness.Internal

theorem receive_keysSampled_payload
    [DecidableEq P.Sym]
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
    (enc : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv P auth ik T (.keysSampled e a sk vec enc))
    (hPayload : MessagePayloadInv P auth ik T msg) :
    ∃ r, receive P auth (.keysSampled e a sk vec enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv P auth ik T r.state := by
  -- Only an epoch-`e` `ct₁` chunk changes the state; every other message is ignored.
  rcases msg with ⟨me, mt, md⟩
  cases mt with
  | ct1 =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some chunk =>
          simp only [MessagePayloadInv] at hPayload
          obtain ⟨encapsState, ct1, key, i, hc, hchunk⟩ := hPayload
          by_cases he : me = e
          · subst me
            refine ⟨⟨e - 1, none, .headerSent e a sk
              ((DecoderState.empty P.ecpCt1).addChunk chunk)
              (EncoderState.init P.ecpEk vec)⟩, ?_, rfl, ?_⟩
            · simp [receive, Message.wellFormed]
            · have hch : chunk = P.ecpCt1.encode ct1 i := Option.some.inj hchunk
              subst hch
              have hadd := DecoderState.addChunk_payloadChunks P.ecpCt1 ct1 ∅ i
              rw [ErasureCodePayload.payloadChunks_empty] at hadd
              obtain ⟨ha, pk, hkp, hvec, -⟩ := hLocal
              exact ⟨ha, pk, encapsState, ct1, key, hkp, hc, ⟨congrArg DecoderState.ecp hadd, _,
                congrArg DecoderState.chunks hadd⟩, rfl, hvec⟩
          · exact ⟨⟨e - 1, none, .keysSampled e a sk vec enc⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

theorem receive_headerSent_payload
    [DecidableEq P.Sym]
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK)
    (dec : DecoderState P.inc.C₁ P.Sym)
    (enc : EncoderState P.inc.PKvector P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv P auth ik T (.headerSent e a sk dec enc))
    (hPayload : MessagePayloadInv P auth ik T msg) :
    ∃ r, receive P auth (.headerSent e a sk dec enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv P auth ik T r.state := by
  -- Only an epoch-`e` `ct₁` chunk changes the state;
  -- `DecoderState.addChunk_encode_of_payloadChunks` splits into the cases where `ct₁` is still
  -- incomplete and where it is complete.
  rcases msg with ⟨me, mt, md⟩
  cases mt with
  | ct1 =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some chunk =>
          by_cases he : me = e
          · subst me
            simp only [MessagePayloadInv] at hPayload
            obtain ⟨es', ct1', key', i, hc', hchunk⟩ := hPayload
            obtain ⟨ha, pk, encapsState, ct1, key, hkp, hc, hdec, henc⟩ := hLocal
            obtain ⟨rfl, rfl, rfl⟩ : encapsState = es' ∧ ct1 = ct1' ∧ key = key' := by
              simpa using hc.symm.trans hc'
            have hch := Option.some.inj hchunk
            have hC :=
              DecoderState.addChunk_encode_of_payloadChunks P.ecpCt1 hCt1Correct _ dec hdec i
            rw [← hch] at hC
            obtain ⟨hecp, ⟨I, hchunks⟩, hnone | hsome⟩ := hC
            · exact ⟨⟨e - 1, none, .headerSent e a sk (dec.addChunk chunk) enc⟩,
                by simp [receive, Message.wellFormed, hnone], rfl,
                ha, pk, encapsState, ct1, key, hkp, hc, ⟨hecp, I, hchunks⟩, henc⟩
            · exact ⟨⟨e - 1, none, .ct1Received e a sk ct1 enc⟩,
                by simp [receive, Message.wellFormed, hsome], rfl,
                ha, pk, encapsState, key, hkp, hc, henc⟩
          · exact ⟨⟨e - 1, none, .headerSent e a sk dec enc⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

theorem receive_ct1Received_payload
    [DecidableEq P.Sym]
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
    (enc : EncoderState P.inc.PKvector P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv P auth ik T (.ct1Received e a sk ct1 enc))
    (hPayload : MessagePayloadInv P auth ik T msg) :
    ∃ r, receive P auth (.ct1Received e a sk ct1 enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv P auth ik T r.state := by
  -- Only an epoch-`e` `ct₂` chunk changes the state: it starts the `ct₂` decoder.
  rcases msg with ⟨me, mt, md⟩
  cases mt with
  | ct2 =>
      cases md with
      | none => exact ⟨_, rfl, rfl, hLocal⟩
      | some chunk =>
          by_cases he : me = e
          · subst me
            simp only [MessagePayloadInv] at hPayload
            obtain ⟨pk', sk', es', ct1', key', i, hkp', hc', hchunk⟩ := hPayload
            obtain ⟨ha, pk, encapsState, key, hkp, hc, -⟩ := hLocal
            obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
            obtain ⟨rfl, rfl, rfl⟩ : encapsState = es' ∧ ct1 = ct1' ∧ key = key' := by
              simpa using hc.symm.trans hc'
            have hch := Option.some.inj hchunk
            have hfirst : ∀ {M : Type} (ecp : ErasureCodePayload M P.Sym) (p : M) (j : ℕ),
                ((DecoderState.empty ecp).addChunk (ecp.encode p j)).ecp = ecp ∧
                  ∃ I : Finset (Fin ecp.ec.N),
                    ((DecoderState.empty ecp).addChunk (ecp.encode p j)).chunks =
                      ErasureCodePayload.payloadChunks ecp p I := by
              intro M ecp p j
              have hadd := DecoderState.addChunk_payloadChunks ecp p ∅ j
              rw [ErasureCodePayload.payloadChunks_empty] at hadd
              exact ⟨congrArg DecoderState.ecp hadd, _, congrArg DecoderState.chunks hadd⟩
            refine ⟨⟨e - 1, none, .ekSentCt1Received e a sk ct1
                ((DecoderState.empty P.ecpCt2).addChunk chunk)⟩,
              by simp [receive, Message.wellFormed], rfl, ha, pk, encapsState, key, hkp, hc, ?_⟩
            rw [hch]
            exact hfirst P.ecpCt2 _ i
          · exact ⟨⟨e - 1, none, .ct1Received e a sk ct1 enc⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

theorem receive_ekSentCt1Received_payload
    [DecidableEq P.Sym]
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
    (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym)
    (peerKeys : ℕ → Option P.EpochKey)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv P auth ik T
      (.ekSentCt1Received e a sk ct1 dec))
    (hPayload : MessagePayloadInv P auth ik T msg)
    (hpos : 0 < e)
    (hKeys : ∀ encapsState key, (T e).encaps1 = some (encapsState, ct1, key) →
      peerKeys e = some (P.kdfOK key e)) :
    let st : State P AuthState := .ekSentCt1Received e a sk ct1 dec
    let outputsAgree := fun r : RecvResult P AuthState =>
      ∀ t outKey, r.outputKey = some (t, outKey) → peerKeys t = some outKey
    (∀ r, receive P auth st msg = .ok r →
      outputsAgree r → LocalPayloadInv P auth ik T r.state) ∧
    ((∀ pk encapsState key,
      (T e).keypair = some (pk, sk) →
      (T e).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey P e pk sk encapsState ct1 = some (P.kdfOK key e)) →
      ∃ r, receive P auth st msg = .ok r ∧ outputsAgree r) ∧
    (∀ r t outKey, receive P auth st msg = .ok r →
      r.outputKey = some (t, outKey) →
      t = e ∧ ∃ pk encapsState key,
        (T e).keypair = some (pk, sk) ∧
        (T e).encaps1 = some (encapsState, ct1, key) ∧
        decapsEpochKey P e pk sk encapsState ct1 = some outKey) := by
  dsimp only
  have hold := hLocal
  obtain ⟨ha, pk, encapsState, key, hkp, hc, hdec⟩ := hLocal
  -- The ciphertext tag of epoch `e` uses the authenticator ratcheted with the recorded key.
  have hauth : transcriptAuth P auth ik T e = auth.update a e (P.kdfOK key e) := by
    obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
    rw [ha]
    simp only [transcriptAuth, hc, Nat.add_sub_cancel]
  have hpeer := hKeys encapsState key hc
  -- Either the receive leaves no key and a payload-consistent state, or it is the recorded
  -- `ct₂` chunk that completes the decoder of the transcript's `ct₂ ‖ tag`.
  have houtcome :
      (∃ st', receive P auth (.ekSentCt1Received e a sk ct1 dec) msg =
          .ok ⟨e - 1, none, st'⟩ ∧ LocalPayloadInv P auth ik T st') ∨
        ∃ chunk, msg = ⟨e, .ct2, some chunk⟩ ∧
          (dec.addChunk chunk).decodedPayload =
            some (P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk),
              auth.macCiphertext (transcriptAuth P auth ik T e) e
                (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) := by
    rcases msg with ⟨me, mt, md⟩
    cases mt with
    | ct2 =>
        cases md with
        | none => exact Or.inl ⟨_, rfl, hold⟩
        | some chunk =>
            by_cases he : me = e
            · subst me
              simp only [MessagePayloadInv] at hPayload
              obtain ⟨pk', sk', es', ct1', key', i, hkp', hc', hchunk⟩ := hPayload
              obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
              obtain ⟨rfl, rfl, rfl⟩ : encapsState = es' ∧ ct1 = ct1' ∧ key = key' := by
                simpa using hc.symm.trans hc'
              have hch := Option.some.inj hchunk
              have hC :=
                DecoderState.addChunk_encode_of_payloadChunks P.ecpCt2 hCt2Correct _ dec hdec i
              rw [← hch] at hC
              obtain ⟨hecp, ⟨I, hchunks⟩, hnone | hsome⟩ := hC
              · exact Or.inl ⟨.ekSentCt1Received e a sk ct1 (dec.addChunk chunk),
                  by simp [receive, Message.wellFormed, hnone],
                  ha, pk, encapsState, key, hkp, hc, hecp, I, hchunks⟩
              · exact Or.inr ⟨chunk, rfl, hsome⟩
            · exact Or.inl ⟨.ekSentCt1Received e a sk ct1 dec,
                by simp [receive, Message.wellFormed, State.epoch, he], hold⟩
    | _ => cases md <;> exact Or.inl ⟨_, rfl, hold⟩
  rcases houtcome with ⟨st', hrecv, hst'⟩ | ⟨chunk, rfl, hsome⟩
  · refine ⟨fun r hr _ => ?_, fun _ => ⟨_, hrecv, fun t key h => by cases h⟩,
      fun r t outKey hr h => ?_⟩
    · rw [hrecv] at hr
      cases hr
      exact hst'
    · rw [hrecv] at hr
      cases hr
      cases h
  · -- A successful receive of the completing chunk outputs the decapsulated epoch key.
    have hB : ∀ r, receive P auth (.ekSentCt1Received e a sk ct1 dec)
        ⟨e, .ct2, some chunk⟩ = .ok r →
        ∃ k, P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
            P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) = some k ∧
          r = ⟨e - 1, some (e, P.kdfOK k e), .noHeaderReceived (e + 1)
            (auth.update a e (P.kdfOK k e)) (DecoderState.empty P.ecpHdr)⟩ := by
      intro r hr
      cases hdk : P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
          P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) with
      | none => simp [receive, Message.wellFormed, hsome, hdk] at hr
      | some k =>
          cases hv : auth.verifyCiphertext (auth.update a e (P.kdfOK k e)) e
              (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))
              (auth.macCiphertext (transcriptAuth P auth ik T e) e
                (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) with
          | false => simp [receive, Message.wellFormed, hsome, hdk, hv] at hr
          | true =>
              have hrecv : receive P auth (.ekSentCt1Received e a sk ct1 dec)
                  ⟨e, .ct2, some chunk⟩ = .ok ⟨e - 1, some (e, P.kdfOK k e),
                    .noHeaderReceived (e + 1) (auth.update a e (P.kdfOK k e))
                      (DecoderState.empty P.ecpHdr)⟩ := by
                simp [receive, Message.wellFormed, hsome, hdk, hv]
              rw [hrecv] at hr
              cases hr
              exact ⟨k, rfl, rfl⟩
    refine ⟨fun r hr hagree => ?_, fun htrial => ?_, fun r t outKey hr hout => ?_⟩
    · obtain ⟨k, -, rfl⟩ := hB r hr
      have hk : P.kdfOK k e = P.kdfOK key e :=
        Option.some.inj ((hagree e _ rfl).symm.trans hpeer)
      refine ⟨?_, ?_⟩
      · rw [Nat.add_sub_cancel, hk, hauth]
      · cases (T (e + 1)).keypair with
        | none => exact rfl
        | some kp => exact ⟨rfl, ∅, (ErasureCodePayload.payloadChunks_empty P.ecpHdr _).symm⟩
    · obtain ⟨k, hdk, hk⟩ : ∃ k, P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
          P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) = some k ∧
          P.kdfOK k e = P.kdfOK key e := by
        have htr := htrial pk encapsState key hkp hc
        unfold decapsEpochKey at htr
        cases hdk : P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
            P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) with
        | none =>
            rw [hdk] at htr
            cases htr
        | some k =>
            rw [hdk] at htr
            exact ⟨k, rfl, Option.some.inj htr⟩
      refine ⟨⟨e - 1, some (e, P.kdfOK k e), .noHeaderReceived (e + 1)
          (auth.update a e (P.kdfOK k e)) (DecoderState.empty P.ecpHdr)⟩, ?_, ?_⟩
      · simp [receive, Message.wellFormed, hsome, hdk, hk, ← hauth,
          auth.verifyCiphertext_correct]
      · intro t outKey hout
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hout)
        rw [hk]
        exact hpeer
    · obtain ⟨k, hdk, rfl⟩ := hB r hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hout)
      exact ⟨rfl, pk, encapsState, key, hkp, hc, by simp [decapsEpochKey, hdk]⟩

theorem generator_peer_key
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s)
    (party : Bool)
    (hgenerator :
      (if party then s.stA else s.stB).controlPosition.isGenerator = true) :
    let st := if party then s.stA else s.stB
    let peerKeys := if party then s.keyB else s.keyA
    ∀ encapsState ct1 key, (T st.epoch).encaps1 = some (encapsState, ct1, key) →
      peerKeys st.epoch = some (P.kdfOK key st.epoch) := by
  rcases hT with ⟨_, hControl, _, _, _, _, hEncaps, _, _, _, hKeys⟩
  cases party
  · dsimp only
    intro encapsState ct1 key hencaps
    simp only [Bool.false_eq_true, ↓reduceIte] at hgenerator hencaps ⊢
    have hB := hControl.roles false
    simp only [Bool.false_eq_true, ↓reduceIte] at hB
    rw [hgenerator] at hB
    have hEven : s.stB.epoch % 2 = 0 :=
      of_decide_eq_true hB.1.symm
    rcases hEncaps s.stB.epoch encapsState ct1 key hencaps with
      ⟨hpos, hbound, -⟩
    have hbound' : s.stB.epoch ≤ s.stA.completedEpoch := by
      simpa [hEven] using hbound
    have htable := hKeys true s.stB.epoch
    simp only [if_true] at htable
    rw [htable]
    simp [hpos, hbound', hencaps]
  · dsimp only
    intro encapsState ct1 key hencaps
    simp only [if_true] at hgenerator hencaps ⊢
    have hA := hControl.roles true
    simp only [if_true] at hA
    rw [hgenerator] at hA
    have hOdd : s.stA.epoch % 2 = 1 :=
      of_decide_eq_true hA.1.symm
    rcases hEncaps s.stA.epoch encapsState ct1 key hencaps with
      ⟨hpos, hbound, -⟩
    have hbound' : s.stA.epoch ≤ s.stB.completedEpoch := by
      simpa [hOdd] using hbound
    have htable := hKeys false s.stA.epoch
    simp only [Bool.false_eq_true, ↓reduceIte] at htable
    rw [htable]
    simp [hpos, hbound', hencaps]

theorem receive_recorded_output
    [DecidableEq P.Sym]
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg :
      (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (if party then s.stA else s.stB) msg = .ok r)
    (t : ℕ) (outKey : P.EpochKey)
    (hout : r.outputKey = some (t, outKey)) :
    t = (if party then s.stA else s.stB).epoch ∧
      (if party then s.stA else s.stB).controlPosition.isGenerator = true ∧
      ∃ pk sk encapsState ct1 key,
        (T t).keypair = some (pk, sk) ∧
        (T t).encaps1 = some (encapsState, ct1, key) ∧
        decapsEpochKey P t pk sk encapsState ct1 = some outKey ∧
        (if party then s.keyB else s.keyA) t = some (P.kdfOK key t) := by
  obtain ⟨-, hControl, -, -, -, -, -, hLocalA, hLocalB, hMessages, -⟩ := id hT
  have hLocal : LocalPayloadInv P auth ik T (if party then s.stA else s.stB) := by
    cases party
    · exact hLocalB
    · exact hLocalA
  have hPayload : MessagePayloadInv P auth ik T msg := by
    cases party
    · exact hMessages true n msg tsnd hmsg
    · exact hMessages false n msg tsnd hmsg
  have hpos : 0 < (if party then s.stA else s.stB).epoch := by
    cases party
    · exact hControl.epochKnowledge.keyPrefix.posB
    · exact hControl.epochKnowledge.keyPrefix.posA
  obtain ⟨st, hst⟩ : ∃ st, (if party then s.stA else s.stB) = st := ⟨_, rfl⟩
  rw [hst] at hr hLocal hpos ⊢
  cases st
  case ekSentCt1Received e a sk ct1 dec =>
    -- Only this state outputs a key; `receive_ekSentCt1Received_payload` gives its value.
    have hgen : (if party then s.stA else s.stB).controlPosition.isGenerator = true := by
      simp only [hst, State.controlPosition]
    have hpeer := generator_peer_key P auth ik T s hT party hgen
    dsimp only at hpeer
    rw [hst] at hpeer
    obtain ⟨-, -, hout4⟩ := receive_ekSentCt1Received_payload P auth hCt2Correct ik T e a sk
      ct1 dec (if party then s.keyB else s.keyA) msg hLocal hPayload hpos
      (fun encapsState key hc => hpeer encapsState ct1 key hc)
    obtain ⟨rfl, pk, encapsState, key, hkp, hc, hkey⟩ := hout4 r t outKey hr hout
    exact ⟨rfl, rfl, pk, sk, encapsState, ct1, key, hkp, hc, hkey, hpeer encapsState ct1 key hc⟩
  all_goals
    -- Every other constructor's successful receives carry no output key.
    exfalso
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals cases hout

end Correctness.Internal

end MLKEMBraid
