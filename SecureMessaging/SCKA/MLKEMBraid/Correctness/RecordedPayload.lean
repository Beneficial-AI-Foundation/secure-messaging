/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.RecordedPayload.Encapsulator

/-!
# Receiving a recorded message

`receive_recorded_payload` combines the key-generator and encapsulator cases. A successful
receive of a recorded message keeps `LocalPayloadInv` when any output key agrees with the peer's
recorded key for that epoch. It succeeds whenever decapsulation at the receiver's epoch derives
the recorded key.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

open Correctness.Internal

theorem receive_recorded_payload
    [DecidableEq P.Sym]
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg :
      (if party then s.msgB else s.msgA) n = some (msg, tsnd)) :
    let st := if party then s.stA else s.stB
    let peerKeys := if party then s.keyB else s.keyA
    let outputsAgree := fun r : RecvResult P AuthState =>
      ∀ e key, r.outputKey = some (e, key) → peerKeys e = some key
    (∀ r, receive P auth st msg = .ok r →
      outputsAgree r → LocalPayloadInv P auth ik T r.state) ∧
    ((∀ pk sk encapsState ct1 key,
      (T st.epoch).keypair = some (pk, sk) →
      (T st.epoch).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey P st.epoch pk sk encapsState ct1 =
                some (P.kdfOK key st.epoch)) →
      ∃ r, receive P auth st msg = .ok r ∧ outputsAgree r) := by
  have hpeer := generator_peer_key P auth ik T s hT party
  dsimp only at hpeer ⊢
  obtain ⟨-, hControl, -, -, -, hKeypair, hEncaps, hLocalA, hLocalB, hMessages, -⟩ := hT
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
  -- An encapsulator at epoch `t` also generates epoch `t + 1`, so the parity expressions for
  -- the encapsulator of `t` and the generator of `t + 1` both select the receiver's state.
  have hF : (if party then s.stA else s.stB).controlPosition.isGenerator = false →
      ∀ t, t = (if party then s.stA else s.stB).epoch →
        (if t % 2 = 1 then s.stB else s.stA) = (if party then s.stA else s.stB) ∧
          (if (t + 1) % 2 = 1 then s.stA else s.stB) = (if party then s.stA else s.stB) := by
    intro hencapsulator t ht
    have hrole := hControl.roles party
    cases party
    · simp only [Bool.false_eq_true, ↓reduceIte] at hrole hencapsulator ht ⊢
      rw [hencapsulator] at hrole
      have hne := of_decide_eq_false hrole.1.symm
      rw [if_pos (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    · simp only [if_true] at hrole hencapsulator ht ⊢
      rw [hencapsulator] at hrole
      have hne := of_decide_eq_false hrole.1.symm
      rw [if_neg (by omega), if_pos (by omega)]
      exact ⟨rfl, rfl⟩
  -- Case on the receiver's state; each case applies the matching lemma of `Generator` or
  -- `Encapsulator`. Only `ekSentCt1Received` can output a key.
  obtain ⟨st, hst⟩ : ∃ st, (if party then s.stA else s.stB) = st := ⟨_, rfl⟩
  obtain ⟨peerKeys, hpk⟩ : ∃ k, (if party then s.keyB else s.keyA) = k := ⟨_, rfl⟩
  rw [hst] at hLocal hpos hpeer hF ⊢
  rw [hpk] at hpeer ⊢
  have hnoKey : ∀ r, receive P auth st msg = .ok r → r.outputKey = none →
      LocalPayloadInv P auth ik T r.state →
      (∀ r', receive P auth st msg = .ok r' →
        (∀ e key, r'.outputKey = some (e, key) → peerKeys e = some key) →
        LocalPayloadInv P auth ik T r'.state) ∧
      ((∀ pk sk encapsState ct1 key,
        (T st.epoch).keypair = some (pk, sk) →
        (T st.epoch).encaps1 = some (encapsState, ct1, key) →
        decapsEpochKey P st.epoch pk sk encapsState ct1 =
                  some (P.kdfOK key st.epoch)) →
        ∃ r', receive P auth st msg = .ok r' ∧
          ∀ e key, r'.outputKey = some (e, key) → peerKeys e = some key) := by
    intro r hr hnone hinv
    refine ⟨fun r' hr' _ => ?_, fun _ => ⟨r, hr, fun e key h => ?_⟩⟩
    · rw [hr] at hr'
      cases hr'
      exact hinv
    · rw [hnone] at h
      cases h
  cases st
  case keysUnsampled e a =>
    have hsame : receive P auth (.keysUnsampled e a) msg =
        .ok ⟨e - 1, none, .keysUnsampled e a⟩ := by
      rcases msg with ⟨me, mt, md⟩
      cases mt <;> cases md <;> rfl
    exact hnoKey _ hsame rfl hLocal
  case keysSampled e a sk vec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_keysSampled_payload P auth ik T e a sk vec enc msg hLocal hPayload
    exact hnoKey r hr hnone hinv
  case headerSent e a sk dec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_headerSent_payload P auth hCt1Correct ik T e a sk dec enc msg hLocal hPayload
    exact hnoKey r hr hnone hinv
  case ct1Received e a sk ct1 enc =>
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_ct1Received_payload P auth ik T e a sk ct1 enc msg hLocal hPayload
    exact hnoKey r hr hnone hinv
  case ekSentCt1Received e a sk ct1 dec =>
    obtain ⟨h1, h2, -⟩ := receive_ekSentCt1Received_payload P auth hCt2Correct ik T e a sk
      ct1 dec peerKeys msg hLocal hPayload hpos
      (fun encapsState key hc => hpeer rfl encapsState ct1 key hc)
    exact ⟨h1, fun h6 => h2 fun pk encapsState key hkp hc => h6 pk sk encapsState ct1 key hkp hc⟩
  case noHeaderReceived e a dec =>
    -- The receiver has not completed epoch `e`, so the transcript has no encapsulation there.
    have hNoEncaps : (T e).encaps1 = none := by
      cases hce : (T e).encaps1 with
      | none => rfl
      | some c =>
          obtain ⟨hpos, hle, -⟩ := hEncaps e c.1 c.2.1 c.2.2 hce
          rw [(hF rfl e rfl).1] at hle
          have hcomp : (State.noHeaderReceived e a dec : State P AuthState).completedEpoch =
              e - 1 := rfl
          omega
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_noHeaderReceived_payload P auth hHdrCorrect ik T e a dec msg hLocal hPayload
        hNoEncaps
    exact hnoKey r hr hnone hinv
  case headerReceived e a hdr dec =>
    exact hnoKey ⟨e - 1, none, .headerReceived e a hdr dec⟩ (by simp [receive, State.epoch])
      rfl hLocal
  case ct1Sampled e a hdr encapsState ct1 enc dec =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ct1Sampled_payload P auth hEkCorrect ik T e a hdr
      encapsState ct1 enc dec msg hLocal hPayload
    exact hnoKey r hr hnone hinv
  case ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ekReceivedCt1Sampled_payload P auth ik T e a
      encapsState ct1 hdr vec enc msg hLocal
    exact hnoKey r hr hnone hinv
  case ct1Acknowledged e a hdr encapsState ct1 dec =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ct1Acknowledged_payload P auth hEkCorrect ik T e a
      hdr encapsState ct1 dec msg hLocal hPayload
    exact hnoKey r hr hnone hinv
  case ct2Sampled e a enc =>
    -- The receiver generates epoch `e + 1` but has not sampled its keys yet.
    have hkp : (T (e + 1)).keypair = none := by
      cases hk : (T (e + 1)).keypair with
      | none => rfl
      | some kp =>
          obtain ⟨-, hle⟩ := hKeypair (e + 1) kp.1 kp.2 hk
          rw [(hF rfl e rfl).2] at hle
          have hep : (State.ct2Sampled e a enc : State P AuthState).epoch = e := rfl
          omega
    have hce : (T (e + 1)).encaps1 = none := by
      cases hc : (T (e + 1)).encaps1 with
      | none => rfl
      | some c =>
          obtain ⟨-, -, pk, sk, hkp', -⟩ := hEncaps (e + 1) c.1 c.2.1 c.2.2 hc
          rw [hkp] at hkp'
          cases hkp'
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_ct2Sampled_payload P auth ik T e a enc msg hLocal ⟨hkp, hce⟩
    exact hnoKey r hr hnone hinv

end MLKEMBraid
