/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant

/-!
# Recorded messages received by a key generator

A successful receive of a recorded message by a key generator keeps `LocalPayloadInv` when any
output key agrees with the peer's recorded key for that epoch. Only `ekSentCt1Received` outputs a
key: the epoch key decapsulated from the recorded ciphertext.
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- Receiving a recorded message in `keysSampled` succeeds without key output and preserves
`LocalPayloadInv`. -/
theorem receive_keysSampled_payload
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
    (enc : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.keysSampled e a sk vec enc))
    (hPayload : MessagePayloadInv auth ik T msg) :
    ∃ r, receive P auth (.keysSampled e a sk vec enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
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
              (P.decCt1.addChunk P.decCt1.empty chunk)
              (EncoderState.init P.ecpEk vec)⟩, ?_, rfl, ?_⟩
            · simp [receive, Message.wellFormed]
            · have hch : chunk = P.ecpCt1.encode ct1 i := Option.some.inj hchunk
              subst hch
              obtain ⟨ha, pk, hkp, hvec, -⟩ := hLocal
              exact ⟨ha, pk, encapsState, ct1, key, hkp, hc,
                (P.decCt1.received_empty P.ecpCt1 ct1).addChunk i, rfl, hvec⟩
          · exact ⟨⟨e - 1, none, .keysSampled e a sk vec enc⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

/-- Receiving a recorded message in `headerSent` succeeds without key output and preserves
`LocalPayloadInv`. -/
theorem receive_headerSent_payload
    (hCt1Sound : P.decCt1.Sound P.ecpCt1)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK)
    (dec : P.decCt1.D)
    (enc : EncoderState P.inc.PKvector P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.headerSent e a sk dec enc))
    (hPayload : MessagePayloadInv auth ik T msg) :
    ∃ r, receive P auth (.headerSent e a sk dec enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
  -- Only an epoch-`e` `ct₁` chunk changes the state;
  -- `Sound.received_addChunk` splits into the cases where the decoder returns no payload
  -- and where it returns `ct₁`.
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
            have hC := hCt1Sound.received_addChunk hdec i
            rw [← hch] at hC
            obtain ⟨hhon, hnone | hsome⟩ := hC
            · exact ⟨⟨e - 1, none, .headerSent e a sk (P.decCt1.addChunk dec chunk) enc⟩,
                by simp [receive, Message.wellFormed, hnone], rfl,
                ha, pk, encapsState, ct1, key, hkp, hc, hhon, henc⟩
            · exact ⟨⟨e - 1, none, .ct1Received e a sk ct1 enc⟩,
                by simp [receive, Message.wellFormed, hsome], rfl,
                ha, pk, encapsState, key, hkp, hc, henc⟩
          · exact ⟨⟨e - 1, none, .headerSent e a sk dec enc⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

/-- Receiving a recorded message in `ct1Received` succeeds without key output and preserves
`LocalPayloadInv`. -/
theorem receive_ct1Received_payload
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
    (enc : EncoderState P.inc.PKvector P.Sym)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.ct1Received e a sk ct1 enc))
    (hPayload : MessagePayloadInv auth ik T msg) :
    ∃ r, receive P auth (.ct1Received e a sk ct1 enc) msg = .ok r ∧
      r.outputKey = none ∧ LocalPayloadInv auth ik T r.state := by
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
            refine ⟨⟨e - 1, none, .ekSentCt1Received e a sk ct1
                (P.decCt2.addChunk P.decCt2.empty chunk)⟩,
              by simp [receive, Message.wellFormed], rfl, ha, pk, encapsState, key, hkp, hc, ?_⟩
            rw [hch]
            exact (P.decCt2.received_empty P.ecpCt2 _).addChunk i
          · exact ⟨⟨e - 1, none, .ct1Received e a sk ct1 enc⟩,
              by simp [receive, Message.wellFormed, State.epoch, he], rfl, hLocal⟩
  | _ => cases md <;> exact ⟨_, rfl, rfl, hLocal⟩

/-- A successful receive preserves `LocalPayloadInv` when output keys agree with the peer's.
Correct decapsulation ensures acceptance; any output key is the decapsulated epoch key. -/
theorem receive_ekSentCt1Received_payload
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
    (dec : P.decCt2.D)
    (peerKeys : ℕ → Option P.EpochKey)
    (msg : Message P.Sym)
    (hLocal : LocalPayloadInv auth ik T (.ekSentCt1Received e a sk ct1 dec))
    (hPayload : MessagePayloadInv auth ik T msg)
    (hpos : 0 < e)
    (hKeys : ∀ encapsState key, (T e).encaps1 = some (encapsState, ct1, key) →
      peerKeys e = some (P.kdfOK key e)) :
    let st : State P AuthState := .ekSentCt1Received e a sk ct1 dec
    let outputsAgree := fun r : RecvResult P AuthState =>
      ∀ t outKey, r.outputKey = some (t, outKey) → peerKeys t = some outKey
    (∀ r, receive P auth st msg = .ok r →
      outputsAgree r → LocalPayloadInv auth ik T r.state) ∧
    ((∀ pk encapsState key,
      (T e).keypair = some (pk, sk) →
      (T e).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey e pk sk encapsState ct1 = some (P.kdfOK key e)) →
      ∃ r, receive P auth st msg = .ok r ∧ outputsAgree r) ∧
    (∀ r t outKey, receive P auth st msg = .ok r →
      r.outputKey = some (t, outKey) →
      t = e ∧ ∃ pk encapsState key,
        (T e).keypair = some (pk, sk) ∧
        (T e).encaps1 = some (encapsState, ct1, key) ∧
        decapsEpochKey e pk sk encapsState ct1 = some outKey) := by
  dsimp only
  have hold := hLocal
  obtain ⟨ha, pk, encapsState, key, hkp, hc, hdec⟩ := hLocal
  -- The ciphertext tag of epoch `e` uses the authenticator ratcheted with the recorded key.
  have hauth : transcriptAuth auth ik T e = auth.update a e (P.kdfOK key e) := by
    obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
    rw [ha]
    simp only [transcriptAuth, hc, Nat.add_sub_cancel]
  have hpeer := hKeys encapsState key hc
  -- Either the receive leaves no key and a payload-consistent state, or it is the recorded
  -- `ct₂` chunk that completes the decoder of the transcript's `ct₂ ‖ tag`.
  have houtcome :
      (∃ st', receive P auth (.ekSentCt1Received e a sk ct1 dec) msg =
          .ok ⟨e - 1, none, st'⟩ ∧ LocalPayloadInv auth ik T st') ∨
        ∃ chunk, msg = ⟨e, .ct2, some chunk⟩ ∧
          P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) =
            some (P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk),
              auth.macCiphertext (transcriptAuth auth ik T e) e
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
              have hC := hCt2Sound.received_addChunk hdec i
              rw [← hch] at hC
              obtain ⟨hhon, hnone | hsome⟩ := hC
              · exact Or.inl ⟨.ekSentCt1Received e a sk ct1 (P.decCt2.addChunk dec chunk),
                  by simp [receive, Message.wellFormed, hnone],
                  ha, pk, encapsState, key, hkp, hc, hhon⟩
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
            (auth.update a e (P.kdfOK k e)) P.decHdr.empty⟩ := by
      intro r hr
      cases hdk : P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
          P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) with
      | none => simp [receive, Message.wellFormed, hsome, hdk] at hr
      | some k =>
          cases hv : auth.verifyCiphertext (auth.update a e (P.kdfOK k e)) e
              (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))
              (auth.macCiphertext (transcriptAuth auth ik T e) e
                (ct1, P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) with
          | false => simp [receive, Message.wellFormed, hsome, hdk, hv] at hr
          | true =>
              have hrecv : receive P auth (.ekSentCt1Received e a sk ct1 dec)
                  ⟨e, .ct2, some chunk⟩ = .ok ⟨e - 1, some (e, P.kdfOK k e),
                    .noHeaderReceived (e + 1) (auth.update a e (P.kdfOK k e))
                      P.decHdr.empty⟩ := by
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
        | some kp => exact P.decHdr.received_empty P.ecpHdr _
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
          (auth.update a e (P.kdfOK k e)) P.decHdr.empty⟩, ?_, ?_⟩
      · simp [receive, Message.wellFormed, hsome, hdk, hk, ← hauth,
          auth.verifyCiphertext_correct]
      · intro t outKey hout
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hout)
        rw [hk]
        exact hpeer
    · obtain ⟨k, hdk, rfl⟩ := hB r hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hout)
      exact ⟨rfl, pk, encapsState, key, hkp, hc, by simp [decapsEpochKey, hdk]⟩

/-- The peer of a generator holds the derived transcript key whenever the current epoch has a
recorded encapsulation. -/
theorem generator_peer_key {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool)
    (hgenerator : (s.stateAt party).controlPosition.isGenerator = true) :
    let st := s.stateAt party
    let peerKeys := s.keysAt (!party)
    ∀ encapsState ct1 key, (T st.epoch).encaps1 = some (encapsState, ct1, key) →
      peerKeys st.epoch = some (P.kdfOK key st.epoch) := by
  dsimp only
  intro encapsState ct1 key hencaps
  have hRole := hT.control.role party
  rw [hgenerator] at hRole
  have hpar := of_decide_eq_true hRole.symm
  obtain ⟨hpos, hbound, -⟩ := hT.encaps _ encapsState ct1 key hencaps
  have hpeer : (if (s.stateAt party).epoch % 2 = 1 then s.stB else s.stA) =
      s.stateAt (!party) := by
    cases party
    · simp only [GameState.stateAt, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hpar ⊢
      rw [ite_eq_right (by omega)]
    · simp only [GameState.stateAt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpar ⊢
      rw [ite_eq_left hpar]
  rw [hpeer] at hbound
  rw [GameState.keysAt, hT.keys (!party), ite_eq_left ⟨hpos, hbound⟩, hencaps]
  rfl

/-- Any output key comes from recorded decapsulation at the generator's epoch; the peer holds the
derived epoch key of the encapsulation. -/
theorem receive_recorded_output
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (s.stateAt party) msg = .ok r)
    (t : ℕ) (outKey : P.EpochKey)
    (hout : r.outputKey = some (t, outKey)) :
    t = (s.stateAt party).epoch ∧
      (s.stateAt party).controlPosition.isGenerator = true ∧
      ∃ pk sk encapsState ct1 key,
        (T t).keypair = some (pk, sk) ∧
        (T t).encaps1 = some (encapsState, ct1, key) ∧
        decapsEpochKey t pk sk encapsState ct1 = some outKey ∧
        s.keysAt (!party) t = some (P.kdfOK key t) := by
  have hLocal := hT.local auth party
  have hPayload := hT.messages (!party) n msg tsnd hmsg
  have hpos := hT.control.epochKnowledge.keyPrefix.pos party
  obtain ⟨st, hst⟩ : ∃ st, s.stateAt party = st := ⟨_, rfl⟩
  rw [hst] at hr hLocal hpos ⊢
  cases st
  case ekSentCt1Received e a sk ct1 dec =>
    -- Only this state outputs a key; `receive_ekSentCt1Received_payload` gives its value.
    have hgen : (s.stateAt party).controlPosition.isGenerator = true := by
      simp only [hst, State.controlPosition]
    have hpeer := generator_peer_key auth hT party hgen
    dsimp only at hpeer
    rw [hst] at hpeer
    obtain ⟨-, -, hout4⟩ := receive_ekSentCt1Received_payload auth hCt2Sound ik T e a sk
      ct1 dec (s.keysAt (!party)) msg hLocal hPayload hpos
      (fun encapsState key hc => hpeer encapsState ct1 key hc)
    obtain ⟨rfl, pk, encapsState, key, hkp, hc, hkey⟩ := hout4 r t outKey hr hout
    exact ⟨rfl, rfl, pk, sk, encapsState, ct1, key, hkp, hc, hkey, hpeer encapsState ct1 key hc⟩
  all_goals
    -- Every other state's receives carry no output key.
    rw [(ReceiveEdge.of_eq_ok auth hr).outputKey_eq_none (fun _ _ _ _ _ h => by cases h)] at hout
    cases hout

end MLKEMBraid
