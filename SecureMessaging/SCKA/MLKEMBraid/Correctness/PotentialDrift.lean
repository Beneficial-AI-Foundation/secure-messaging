/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.Risk
import SecureMessaging.SCKA.MLKEMBraid.Correctness.SendInvariant
import SecureMessaging.SCKA.MLKEMBraid.Correctness.ReceiveInvariant

/-!
# Drift of the failure potential

One query of the correctness game raises the expected `failurePotential` by at most the KEM
correctness error for a send query and not at all otherwise
(`expectedPayoff_failurePotential_query_le`). The cases:

* a send that samples a key pair has expected potential exactly the correctness error, since the
  potential of the new state is `decapsFailureProb` of the sampled pair
  (`expectedPayoff_failurePotential_send_keysUnsampled`);
* a send that encapsulates turns `decapsFailureProb` into the indicator `derivedKeyFailure`, whose
  expectation is at most it (`expectedPayoff_failurePotential_send_headerReceived_le`);
* every other send keeps the potential (`send_correct_and_currentEpochFailure_eq`);
* a receive clears the correctness flag only when the potential is already `1`
  (`recv_correct_of_decaps_eq`), keeps it when both epochs stay
  (`recv_currentEpochFailure_le_of_epochs_eq`), and sets it to `0` when an epoch advances
  (`recv_currentEpochFailure_eq_zero_of_epoch_ne`).
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec
open ENNReal

namespace MLKEMBraid

variable {P : Parameters ProbComp} [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

omit [DecidableEq P.Sym] in
/-- `derivedKeyFailure` is at most the indicator that decapsulation does not return the KEM
key. -/
private theorem derivedKeyFailure_le
    (e : ℕ) (pk : P.PK) (sk : P.SK) (encapsState : P.inc.St) (ct1 : P.inc.C₁) (key : P.K) :
    derivedKeyFailure e sk ct1
        (P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))
        (P.kdfOK key e) ≤
      if P.hDet.decapsDet sk
          (P.inc.splitC.symm (ct1,
            P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) =
          some key
      then 0 else 1 := by
  unfold derivedKeyFailure
  by_cases hb : P.hDet.decapsDet sk
      (P.inc.splitC.symm (ct1,
        P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))) = some key
  · simp [hb]
  · rw [if_neg hb]
    split_ifs <;> simp

omit [DecidableEq P.Sym] in
/-- The failure potential is at most `1`. -/
private theorem failurePotential_le_one (s : GameState P AuthState) :
    failurePotential s ≤ 1 := by
  have hrisk : ∀ hdr vec sk, P.inc.decapsFailureProb P.hDet P.hEnc2 hdr vec sk ≤ 1 :=
    fun hdr vec sk => expectedPayoff_le_one _ _ fun _ => by split; split_ifs <;> simp
  have hderived : ∀ e sk ct1 ct2 key, derivedKeyFailure (P := P) e sk ct1 ct2 key ≤ 1 := by
    intro e sk ct1 ct2 key
    unfold derivedKeyFailure
    split_ifs <;> simp
  unfold failurePotential currentEpochFailure pairFailure
  dsimp only
  split_ifs
  all_goals first
    | exact le_rfl
    | exact zero_le_one
    | (split <;> first
        | exact zero_le_one
        | exact hrisk _ _ _
        | (split <;> first | exact zero_le_one | exact hderived _ _ _ _ _))

omit [DecidableEq P.Sym] in
/-- If `currentEpochFailure` is not `1`, decapsulation at either party's epoch derives the key
that its encapsulator recorded. -/
private theorem decaps_eq_of_currentEpochFailure_ne_one
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s)
    (hpot : currentEpochFailure s ≠ 1) (party : Bool) :
    ∀ pk sk encapsState ct1 key,
      (T (if party then s.stA else s.stB).epoch).keypair = some (pk, sk) →
      (T (if party then s.stA else s.stB).epoch).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey (if party then s.stA else s.stB).epoch pk sk encapsState ct1 =
        some (P.kdfOK key (if party then s.stA else s.stB).epoch) := by
  -- At equal epochs `currentEpochFailure` is `derivedKeyFailure` of the recorded samples. At
  -- different epochs both completed epochs equal the lower epoch, so the decapsulation clause
  -- of `TranscriptConsistent.encaps` applies.
  have hformula := currentEpochFailure_eq_transcript auth hT
  obtain ⟨-, hControl, hPair, -, -, -, hEncaps, -, -, -, -⟩ := hT
  intro pk sk es ct1 key hkp hc
  by_cases hep : s.stA.epoch = s.stB.epoch
  · have he : (if party then s.stA else s.stB).epoch = s.stA.epoch := by
      cases party
      · exact hep.symm
      · rfl
    rw [he] at hkp hc ⊢
    rw [if_pos hep] at hformula
    simp only [hkp, hc] at hformula
    rw [hformula] at hpot
    unfold derivedKeyFailure at hpot
    split_ifs at hpot with hd
    · exact hd
    · exact absurd rfl hpot
  · have hcrossA := hControl.epochKnowledge.epochA_le
    have hcrossB := hControl.epochKnowledge.epochB_le
    have hA := s.stA.completedEpoch_le_epoch
    have hB := s.stB.completedEpoch_le_epoch
    obtain ⟨e0, hcA, hcB⟩ :
        ∃ e0, s.stA.completedEpoch = e0 ∧ s.stB.completedEpoch = e0 := by
      rcases Nat.lt_or_gt_of_ne hep with hlt | hgt
      · obtain ⟨hposA, hposB⟩ := hPair.1.2 (by omega)
        refine ⟨s.stA.epoch, ?_, ?_⟩
        · rw [s.stA.completedEpoch_eq, hposA]
          simp
        · rw [s.stB.completedEpoch_eq, hposB]
          simp
          omega
      · obtain ⟨hposB, hposA⟩ := hPair.2.2 (by omega)
        refine ⟨s.stB.epoch, ?_, ?_⟩
        · rw [s.stA.completedEpoch_eq, hposA]
          simp
          omega
        · rw [s.stB.completedEpoch_eq, hposB]
          simp
    generalize (if party then s.stA else s.stB).epoch = e at hkp hc ⊢
    obtain ⟨-, hbound, pk', sk', hkp', hdec⟩ := hEncaps e es ct1 key hc
    have h1 : (if e % 2 = 1 then s.stB else s.stA).completedEpoch = e0 := by
      split_ifs <;> assumption
    have h2 : (if e % 2 = 1 then s.stA else s.stB).completedEpoch = e0 := by
      split_ifs <;> assumption
    rw [h1] at hbound
    rw [hkp] at hkp'
    cases hkp'
    exact hdec (by rw [h2]; exact hbound)

omit [DecidableEq P.K] in
/-- A receive keeps the flag true if decapsulation at its epoch gives the recorded key. -/
private theorem recv_correct_of_decaps_eq
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (hgood : ∀ pk sk encapsState ct1 key,
      (T (if party then s.stA else s.stB).epoch).keypair = some (pk, sk) →
      (T (if party then s.stA else s.stB).epoch).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey (if party then s.stA else s.stB).epoch pk sk encapsState ct1 =
        some (P.kdfOK key (if party then s.stA else s.stB).epoch))
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      (((if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)) n).run s)) :
    z.2.correct = true := by
  -- `receive_recorded_payload` gives a successful receive whose output key agrees with the
  -- peer. The report matches the recorded epoch, a new key is at an unused epoch, and the
  -- completed epoch covers the known prefix.
  have hControl := hT.control
  cases party
  · change z ∈ support ((SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s)
      at hz
    rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, hentry, hraw, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hT.correct
    all_goals
      obtain ⟨r₀, hr₀, hagree⟩ :=
        (receive_recorded_payload auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct hT false n
          msg tsnd hentry).2 hgood
      simp only [Bool.false_eq_true, ↓reduceIte] at hr₀ hagree
    · rw [hr₀] at hraw
      cases hraw
    rw [Except.ok.inj (hr₀.symm.trans hraw)] at hagree
    have hr := hraw
    have hrep : tsnd = msg.epoch - 1 := hControl.recordedReport.msgA n msg tsnd hentry
    have hbound : msg.epoch ≤ s.stB.completedEpoch + 1 :=
      (hControl.epochKnowledge.msgA n msg tsnd hentry).2.1
    have htcur : s.tcurB ≤ s.stB.completedEpoch := hControl.epochKnowledge.tcurB_le
    have hkeyB := hControl.epochKnowledge.keyPrefix.prefixB
    have hmax : max s.tcurB (msg.epoch - 1) ≤ s.stB.completedEpoch := by omega
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.recvBUpdate, Bool.and_eq_true]
      exact ⟨⟨hT.correct, by simp [hrep]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => (hkeyB t).2 ⟨h0, hle.trans hmax⟩⟩
    · have hstep := ((ReceiveEdge.of_eq_ok auth hr).completedEpoch
        hControl.epochKnowledge.keyPrefix.posB).2
      simp only [hkey] at hstep
      obtain ⟨htI, -⟩ := hstep
      have hnone : s.keyB tI = none := by
        by_contra hne
        have := ((hkeyB tI).1 hne).2
        omega
      have hpeer : s.keyA tI = some key := hagree tI key hkey
      simp only [SCKAScheme.recvBUpdate, Bool.and_eq_true]
      refine ⟨⟨⟨⟨hT.correct, by simp [hrep]⟩, by simp [hnone]⟩, by simp [hpeer]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => ?_⟩
      have hle' := hle.trans hmax
      rw [Function.update_of_ne (by omega)]
      exact (hkeyB t).2 ⟨h0, hle'⟩
  · change z ∈ support ((SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s)
      at hz
    rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, hentry, hraw, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hT.correct
    all_goals
      obtain ⟨r₀, hr₀, hagree⟩ :=
        (receive_recorded_payload auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct hT true n
          msg tsnd hentry).2 hgood
      simp only [↓reduceIte] at hr₀ hagree
    · rw [hr₀] at hraw
      cases hraw
    rw [Except.ok.inj (hr₀.symm.trans hraw)] at hagree
    have hr := hraw
    have hrep : tsnd = msg.epoch - 1 := hControl.recordedReport.msgB n msg tsnd hentry
    have hbound : msg.epoch ≤ s.stA.completedEpoch + 1 :=
      (hControl.epochKnowledge.msgB n msg tsnd hentry).2.1
    have htcur : s.tcurA ≤ s.stA.completedEpoch := hControl.epochKnowledge.tcurA_le
    have hkeyA := hControl.epochKnowledge.keyPrefix.prefixA
    have hmax : max s.tcurA (msg.epoch - 1) ≤ s.stA.completedEpoch := by omega
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.recvAUpdate, Bool.and_eq_true]
      exact ⟨⟨hT.correct, by simp [hrep]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => (hkeyA t).2 ⟨h0, hle.trans hmax⟩⟩
    · have hstep := ((ReceiveEdge.of_eq_ok auth hr).completedEpoch
        hControl.epochKnowledge.keyPrefix.posA).2
      simp only [hkey] at hstep
      obtain ⟨htI, -⟩ := hstep
      have hnone : s.keyA tI = none := by
        by_contra hne
        have := ((hkeyA tI).1 hne).2
        omega
      have hpeer : s.keyB tI = some key := hagree tI key hkey
      simp only [SCKAScheme.recvAUpdate, Bool.and_eq_true]
      refine ⟨⟨⟨⟨hT.correct, by simp [hrep]⟩, by simp [hnone]⟩, by simp [hpeer]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => ?_⟩
      have hle' := hle.trans hmax
      rw [Function.update_of_ne (by omega)]
      exact (hkeyA t).2 ⟨h0, hle'⟩

/-- A send that samples a key pair has expected potential equal to the KEM correctness error. -/
private theorem expectedPayoff_failurePotential_send_keysUnsampled
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) {e : ℕ} {a : AuthState}
    (hst : (if party then s.stA else s.stB) = .keysUnsampled e a) :
    expectedPayoff
        (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)
        (fun z => failurePotential z.2) =
      P.kem.correctnessError ProbCompRuntime.probComp := by
  -- Every sampled key pair keeps the flag true and gives potential `decapsFailureProb` of that
  -- pair; its average over key generation is the correctness error.
  obtain ⟨b, dec, hpeer⟩ := peer_noHeaderReceived_of_keysUnsampled auth hT party hst
  have hcorr : s.correct = true := hT.correct
  have hControl := hT.control
  rw [← P.inc.expectedPayoff_keygen_decapsFailureProb P.hDet P.hEnc2]
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hpeer ⊢
    have htcur : s.tcurB ≤ e - 1 := by
      have h := hControl.tcurB_le_sub_one
      rw [hst] at h
      exact h
    have hkeys : ∀ t, 0 < t → t ≤ e - 1 → s.keyB t ≠ none := by
      intro t h0 hle
      refine (hControl.epochKnowledge.keyPrefix.prefixB t).2 ⟨h0, ?_⟩
      rw [hst]
      exact hle
    rw [oracleSendB_run_eq auth irl sampleInitKey, expectedPayoff_map, hst,
      send_keysUnsampled_eq, expectedPayoff_map]
    congr 1
    funext kp
    obtain ⟨pk, sk⟩ := kp
    simp only [SCKAScheme.sendBUpdate]
    unfold failurePotential
    split_ifs with hflag
    · simp [currentEpochFailure, pairFailure, hpeer, State.controlPosition, State.epoch,
        EncoderState.nextChunk, EncoderState.init]
    · exfalso
      apply hflag
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hcorr, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
  · simp only [↓reduceIte] at hst hpeer ⊢
    have htcur : s.tcurA ≤ e - 1 := by
      have h := hControl.tcurA_le_sub_one
      rw [hst] at h
      exact h
    have hkeys : ∀ t, 0 < t → t ≤ e - 1 → s.keyA t ≠ none := by
      intro t h0 hle
      refine (hControl.epochKnowledge.keyPrefix.prefixA t).2 ⟨h0, ?_⟩
      rw [hst]
      exact hle
    rw [oracleSendA_run_eq auth irl sampleInitKey, expectedPayoff_map, hst,
      send_keysUnsampled_eq, expectedPayoff_map]
    congr 1
    funext kp
    obtain ⟨pk, sk⟩ := kp
    simp only [SCKAScheme.sendAUpdate]
    unfold failurePotential
    split_ifs with hflag
    · simp [currentEpochFailure, pairFailure, hpeer, State.controlPosition, State.epoch,
        EncoderState.nextChunk, EncoderState.init]
    · exfalso
      apply hflag
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hcorr, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩

/-- Encapsulating against the recorded key pair has expected potential at most
`currentEpochFailure`. -/
private theorem expectedPayoff_failurePotential_send_headerReceived_le
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) {e : ℕ} {a : AuthState}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : (if party then s.stA else s.stB) = .headerReceived e a hdr dec) :
    expectedPayoff
        (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)
        (fun z => failurePotential z.2) ≤
      currentEpochFailure s := by
  -- `currentEpochFailure` is `decapsFailureProb` of the recorded key pair. Each encapsulation
  -- keeps the flag true and gives potential `derivedKeyFailure`, which is at most the failure of
  -- decapsulation (`derivedKeyFailure_le`).
  obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ := peer_keysSampled_of_headerReceived auth hT party hst
  subst hhdr
  have hcorr : s.correct = true := hT.correct
  have hControl := hT.control
  have hLocal : LocalPayloadInv auth ik T (if party then s.stA else s.stB) := by
    cases party
    · exact hT.localB
    · exact hT.localA
  rw [hst] at hLocal
  simp only [LocalPayloadInv] at hLocal
  obtain ⟨-, hc0, -⟩ := hLocal
  have hep : s.stA.epoch = e ∧ s.stB.epoch = e := by
    cases party
    · exact ⟨congrArg State.epoch hpeer, congrArg State.epoch hst⟩
    · exact ⟨congrArg State.epoch hst, congrArg State.epoch hpeer⟩
  have hΦ : currentEpochFailure s =
      P.inc.decapsFailureProb P.hDet P.hEnc2 (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
    rw [currentEpochFailure_eq_transcript auth hT, if_pos (hep.1.trans hep.2.symm)]
    simp only [hep.1, hkpT, hc0]
  rw [hΦ]
  unfold KEMScheme.IncrementalStructure.decapsFailureProb
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hpeer ⊢
    have hpos : 0 < e := by
      have h := hControl.epochKnowledge.keyPrefix.posB
      rw [hst] at h
      exact h
    have htcur : s.tcurB ≤ e - 1 := by
      have h := hControl.tcurB_le_sub_one
      rw [hst] at h
      exact h
    have hBnone : s.keyB e = none := by
      by_contra hne
      have h := ((hControl.epochKnowledge.keyPrefix.prefixB e).1 hne).2
      rw [hst] at h
      change e ≤ e - 1 at h
      omega
    have hAnone : s.keyA e = none := by
      by_contra hne
      have h := ((hControl.epochKnowledge.keyPrefix.prefixA e).1 hne).2
      rw [hpeer] at h
      change e ≤ e - 1 at h
      omega
    have hkeys : ∀ t, 0 < t → t ≤ e - 1 → s.keyB t ≠ none := by
      intro t h0 hle
      refine (hControl.epochKnowledge.keyPrefix.prefixB t).2 ⟨h0, ?_⟩
      rw [hst]
      exact hle
    rw [oracleSendB_run_eq auth irl sampleInitKey, expectedPayoff_map, hst,
      send_headerReceived_eq, expectedPayoff_map]
    refine expectedPayoff_mono _ _ _ fun c => ?_
    obtain ⟨es, ct1, k⟩ := c
    simp only [SCKAScheme.sendBUpdate]
    have hd := derivedKeyFailure_le e pk sk es ct1 k
    refine le_trans (le_of_eq ?_) hd
    unfold failurePotential
    split_ifs with hflag
    · simp [currentEpochFailure, pairFailure, hpeer, State.controlPosition, State.epoch]
    · exfalso
      apply hflag
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨hcorr, htcur⟩, by simp [hBnone]⟩, by simp [hAnone]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => ?_⟩
      rw [Function.update_of_ne (by omega)]
      exact hkeys t h0 hle
  · simp only [↓reduceIte] at hst hpeer ⊢
    have hpos : 0 < e := by
      have h := hControl.epochKnowledge.keyPrefix.posA
      rw [hst] at h
      exact h
    have htcur : s.tcurA ≤ e - 1 := by
      have h := hControl.tcurA_le_sub_one
      rw [hst] at h
      exact h
    have hAnone : s.keyA e = none := by
      by_contra hne
      have h := ((hControl.epochKnowledge.keyPrefix.prefixA e).1 hne).2
      rw [hst] at h
      change e ≤ e - 1 at h
      omega
    have hBnone : s.keyB e = none := by
      by_contra hne
      have h := ((hControl.epochKnowledge.keyPrefix.prefixB e).1 hne).2
      rw [hpeer] at h
      change e ≤ e - 1 at h
      omega
    have hkeys : ∀ t, 0 < t → t ≤ e - 1 → s.keyA t ≠ none := by
      intro t h0 hle
      refine (hControl.epochKnowledge.keyPrefix.prefixA t).2 ⟨h0, ?_⟩
      rw [hst]
      exact hle
    rw [oracleSendA_run_eq auth irl sampleInitKey, expectedPayoff_map, hst,
      send_headerReceived_eq, expectedPayoff_map]
    refine expectedPayoff_mono _ _ _ fun c => ?_
    obtain ⟨es, ct1, k⟩ := c
    simp only [SCKAScheme.sendAUpdate]
    have hd := derivedKeyFailure_le e pk sk es ct1 k
    refine le_trans (le_of_eq ?_) hd
    unfold failurePotential
    split_ifs with hflag
    · simp [currentEpochFailure, pairFailure, hpeer, State.controlPosition, State.epoch]
    · exfalso
      apply hflag
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨hcorr, htcur⟩, by simp [hAnone]⟩, by simp [hBnone]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => ?_⟩
      rw [Function.update_of_ne (by omega)]
      exact hkeys t h0 hle

/-- A send that samples nothing keeps the flag true and `currentEpochFailure` unchanged. -/
private theorem send_correct_and_currentEpochFailure_eq
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool)
    (hsteady : (if party then s.stA else s.stB).SendsNoSample)
    (z : Option (ℕ × Option ℕ × Message P.Sym) × GameState P AuthState)
    (hz : z ∈ support
      (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)) :
    z.2.correct = true ∧ currentEpochFailure z.2 = currentEpochFailure s := by
  -- The sender only advances an encoder or keeps its state, emits no key, and reports the
  -- epoch before its current one.
  have hcorr : s.correct = true := hT.correct
  have hControl := hT.control
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsteady hz
    have htcur : s.tcurB ≤ s.stB.epoch - 1 := hControl.tcurB_le_sub_one
    have hkeys : ∀ t, 0 < t → t ≤ s.stB.epoch - 1 → s.keyB t ≠ none := fun t h0 hle =>
      (hControl.epochKnowledge.keyPrefix.prefixB t).2
        ⟨h0, hle.trans s.stB.epoch_sub_one_le_completedEpoch⟩
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendB_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    have hsend : r.sendingEpoch = s.stB.epoch - 1 := hedge.sendingEpoch_eq
    -- The sender's state keeps its constructor, so the pair of states keeps its failure value.
    have hshape : r.outputKey = none ∧
        ∀ s0 : GameState P AuthState,
          s0.stA = s.stA → s0.keyA = s.keyA → s0.keyB = s.keyB → s0.stB = r.state →
            currentEpochFailure s0 = currentEpochFailure s := by
      cases hB : s.stB
      all_goals try simp [hB, State.SendsNoSample] at hsteady
      all_goals rw [hB] at hedge
      all_goals cases hedge
      all_goals refine ⟨rfl, fun s0 hA0 hkA hkB hB0 => ?_⟩
      all_goals unfold currentEpochFailure pairFailure
      all_goals rw [hA0, hkA, hkB, hB0, hB]
      all_goals first
        | rfl
        | (cases s.stA <;>
            simp [State.controlPosition, State.epoch, EncoderState.nextChunk])
    simp only [SCKAScheme.sendBUpdate, hshape.1]
    refine ⟨?_, hshape.2 _ rfl rfl rfl rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hsend]
    exact ⟨⟨hcorr, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
  · simp only [↓reduceIte] at hsteady hz
    have htcur : s.tcurA ≤ s.stA.epoch - 1 := hControl.tcurA_le_sub_one
    have hkeys : ∀ t, 0 < t → t ≤ s.stA.epoch - 1 → s.keyA t ≠ none := fun t h0 hle =>
      (hControl.epochKnowledge.keyPrefix.prefixA t).2
        ⟨h0, hle.trans s.stA.epoch_sub_one_le_completedEpoch⟩
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendA_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    have hsend : r.sendingEpoch = s.stA.epoch - 1 := hedge.sendingEpoch_eq
    have hshape : r.outputKey = none ∧
        ∀ s0 : GameState P AuthState,
          s0.stB = s.stB → s0.keyA = s.keyA → s0.keyB = s.keyB → s0.stA = r.state →
            currentEpochFailure s0 = currentEpochFailure s := by
      cases hA : s.stA
      all_goals try simp [hA, State.SendsNoSample] at hsteady
      all_goals rw [hA] at hedge
      all_goals cases hedge
      all_goals refine ⟨rfl, fun s0 hB0 hkA hkB hA0 => ?_⟩
      all_goals unfold currentEpochFailure pairFailure
      all_goals rw [hB0, hkA, hkB, hA0, hA]
      all_goals first
        | rfl
        | (cases s.stB <;>
            simp [State.controlPosition, State.epoch, EncoderState.nextChunk])
    simp only [SCKAScheme.sendAUpdate, hshape.1]
    refine ⟨?_, hshape.2 _ rfl rfl rfl rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hsend]
    exact ⟨⟨hcorr, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩

/-- A successful receive that keeps both epochs does not raise `currentEpochFailure`. -/
private theorem recv_currentEpochFailure_le_of_epochs_eq
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      (((if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)) n).run s))
    (hzc : z.2.correct = true)
    (hepA : z.2.stA.epoch = s.stA.epoch) (hepB : z.2.stB.epoch = s.stB.epoch) :
    currentEpochFailure z.2 ≤ currentEpochFailure s := by
  have hTz := oracleRecv_preserves_transcriptConsistent auth irl sampleInitKey hHdrCorrect
    hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc
  rw [currentEpochFailure_eq_transcript auth hTz, currentEpochFailure_eq_transcript auth hT,
    hepA, hepB]

/-- A successful receive that changes an epoch leaves `currentEpochFailure` equal to `0`. -/
private theorem recv_currentEpochFailure_eq_zero_of_epoch_ne
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      (((if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)) n).run s))
    (hzc : z.2.correct = true)
    (hchange : z.2.stA.epoch ≠ s.stA.epoch ∨ z.2.stB.epoch ≠ s.stB.epoch) :
    currentEpochFailure z.2 = 0 := by
  -- Only the receiver moves. Finishing `ct₂` leaves the receiver one epoch ahead of its peer.
  -- A next-epoch message leaves the new generator with no sampled key pair.
  have hTz := oracleRecv_preserves_transcriptConsistent auth irl sampleInitKey hHdrCorrect
    hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc
  rw [currentEpochFailure_eq_transcript auth hTz]
  cases party
  · change z ∈ support ((SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s)
      at hz
    rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, hzeq⟩
    · simp at hchange
    · cases hzc
    have hedge := ReceiveEdge.of_eq_ok auth hraw
    have hzAB : z.2.stA = s.stA ∧ z.2.stB = r.state := by
      rw [hzeq]
      rcases r.outputKey with _ | ⟨tI, key⟩ <;> simp [SCKAScheme.recvBUpdate]
    obtain ⟨hzA, hzB⟩ := hzAB
    have hne : r.state.epoch ≠ s.stB.epoch := by
      rcases hchange with h | h
      · exact absurd (congrArg State.epoch hzA) h
      · rwa [hzB] at h
    split_ifs with hzep
    · rcases hedge.advance hne with ⟨-, -, a', hks⟩ | ⟨hgen, -, -, a', dec', hnh⟩
      · -- The receiver generates the next epoch and has not sampled its key pair.
        have hLB := hTz.localB
        rw [hzB, hks] at hLB
        simp only [LocalPayloadInv] at hLB
        obtain ⟨-, hkp0, -⟩ := hLB
        have he : z.2.stA.epoch = s.stB.epoch + 1 :=
          hzep.trans ((congrArg State.epoch hzB).trans (congrArg State.epoch hks))
        simp only [he, hkp0]
      · -- A key generator one epoch ahead of its peer contradicts the pair invariant.
        exfalso
        have h1 : s.stA.epoch = s.stB.epoch + 1 :=
          ((congrArg State.epoch hzA).symm.trans hzep).trans
            ((congrArg State.epoch hzB).trans (congrArg State.epoch hnh))
        rw [(hT.statePair.2.2 h1).1] at hgen
        simp at hgen
    · rfl
  · change z ∈ support ((SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s)
      at hz
    rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, hzeq⟩
    · simp at hchange
    · cases hzc
    have hedge := ReceiveEdge.of_eq_ok auth hraw
    have hzAB : z.2.stA = r.state ∧ z.2.stB = s.stB := by
      rw [hzeq]
      rcases r.outputKey with _ | ⟨tI, key⟩ <;> simp [SCKAScheme.recvAUpdate]
    obtain ⟨hzA, hzB⟩ := hzAB
    have hne : r.state.epoch ≠ s.stA.epoch := by
      rcases hchange with h | h
      · rwa [hzA] at h
      · exact absurd (congrArg State.epoch hzB) h
    split_ifs with hzep
    · rcases hedge.advance hne with ⟨-, -, a', hks⟩ | ⟨hgen, -, -, a', dec', hnh⟩
      · have hLA := hTz.localA
        rw [hzA, hks] at hLA
        simp only [LocalPayloadInv] at hLA
        obtain ⟨-, hkp0, -⟩ := hLA
        have he : z.2.stA.epoch = s.stA.epoch + 1 :=
          (congrArg State.epoch hzA).trans (congrArg State.epoch hks)
        simp only [he, hkp0]
      · exfalso
        have h1 : s.stB.epoch = s.stA.epoch + 1 :=
          ((congrArg State.epoch hzB).symm.trans hzep.symm).trans
            ((congrArg State.epoch hzA).trans (congrArg State.epoch hnh))
        rw [(hT.statePair.1.2 h1).1] at hgen
        simp at hgen
    · rfl

/-- A send query raises the expected potential by at most the KEM correctness error. -/
private theorem expectedPayoff_failurePotential_send_le
    (ik : InitKey) (s : GameState P AuthState)
    (hs : CorrectnessInv auth ik s) (party : Bool) :
    expectedPayoff
        (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)
        (fun z => failurePotential z.2) ≤
      failurePotential s + P.kem.correctnessError ProbCompRuntime.probComp := by
  rcases hs with hsf | ⟨T, hT⟩
  · have h1 : failurePotential s = 1 := by simp [failurePotential, hsf]
    rw [h1]
    refine le_trans ?_ le_self_add
    exact expectedPayoff_le_one _ _ fun z => failurePotential_le_one z.2
  have hF : failurePotential s = currentEpochFailure s := by
    simp [failurePotential, hT.correct]
  cases hst : (if party then s.stA else s.stB) with
  | keysUnsampled e a =>
      rw [expectedPayoff_failurePotential_send_keysUnsampled auth irl sampleInitKey hT party hst]
      exact le_add_self
  | headerReceived e a hdr dec =>
      rw [hF]
      exact (expectedPayoff_failurePotential_send_headerReceived_le auth irl sampleInitKey hT party
        hst).trans le_self_add
  | _ =>
      refine le_trans ?_ le_self_add
      refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun z hz => ?_
      obtain ⟨hzc, hpot⟩ := send_correct_and_currentEpochFailure_eq auth irl sampleInitKey hT
        party (by rw [hst]; trivial) z hz
      simp [failurePotential, hzc, hpot, hT.correct]

/-- A receive query does not raise the expected potential. -/
private theorem expectedPayoff_failurePotential_recv_le
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (s : GameState P AuthState)
    (hs : CorrectnessInv auth ik s) (party : Bool) (n : ℕ) :
    expectedPayoff
        (((if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)) n).run s)
        (fun z => failurePotential z.2) ≤
      failurePotential s := by
  rcases hs with hsf | ⟨T, hT⟩
  · have h1 : failurePotential s = 1 := by simp [failurePotential, hsf]
    rw [h1]
    exact expectedPayoff_le_one _ _ fun z => failurePotential_le_one z.2
  have hF : failurePotential s = currentEpochFailure s := by
    simp [failurePotential, hT.correct]
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun z hz => ?_
  rw [hF]
  cases hzc : z.2.correct
  · -- A receive clears the flag only if decapsulation at the receiver's epoch does not return
    -- the recorded key.
    have h : currentEpochFailure s = 1 := by
      by_contra hne
      simpa [hzc] using recv_correct_of_decaps_eq auth irl sampleInitKey hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct hT party n
        (decaps_eq_of_currentEpochFailure_ne_one auth hT hne party) z hz
    simp [failurePotential, hzc, h]
  · simp only [failurePotential, hzc, if_true]
    by_cases h : z.2.stA.epoch = s.stA.epoch ∧ z.2.stB.epoch = s.stB.epoch
    · exact recv_currentEpochFailure_le_of_epochs_eq auth irl sampleInitKey hHdrCorrect
        hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc h.1 h.2
    · rw [recv_currentEpochFailure_eq_zero_of_epoch_ne auth irl sampleInitKey hHdrCorrect
        hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc (not_and_or.mp h)]
      exact zero_le

/-- One query of the correctness game raises the expected failure potential by at most the
KEM correctness error for a send query, and not at all for other queries. The state must
satisfy the correctness invariant, and the four erasure codes must be correct. -/
theorem expectedPayoff_failurePotential_query_le
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Domain)
    (s : GameState P AuthState)
    (hs : CorrectnessInv auth ik s) :
    expectedPayoff
        ((SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey) t).run s)
        (fun z => failurePotential z.2) ≤
      failurePotential s +
        if SCKAScheme.isSendQuery (Rho := Message P.Sym) t
        then P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
  match t with
  | SCKAScheme.sckaCorrectnessSpec.OUnif n =>
      rw [if_neg (by simp [SCKAScheme.isSendQuery]), add_zero]
      refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun z hz => ?_
      exact le_of_eq (congrArg failurePotential
        (SCKAScheme.oracleUnif_preservesInv (· = s) n s rfl z hz))
  | SCKAScheme.sckaCorrectnessSpec.OSendA =>
      rw [if_pos (by simp [SCKAScheme.isSendQuery])]
      exact expectedPayoff_failurePotential_send_le auth irl sampleInitKey ik s hs true
  | SCKAScheme.sckaCorrectnessSpec.OSendB =>
      rw [if_pos (by simp [SCKAScheme.isSendQuery])]
      exact expectedPayoff_failurePotential_send_le auth irl sampleInitKey ik s hs false
  | SCKAScheme.sckaCorrectnessSpec.ORecvA n =>
      rw [if_neg (by simp [SCKAScheme.isSendQuery]), add_zero]
      exact expectedPayoff_failurePotential_recv_le auth irl sampleInitKey hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik s hs true n
  | SCKAScheme.sckaCorrectnessSpec.ORecvB n =>
      rw [if_neg (by simp [SCKAScheme.isSendQuery]), add_zero]
      exact expectedPayoff_failurePotential_recv_le auth irl sampleInitKey hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik s hs false n

end MLKEMBraid
