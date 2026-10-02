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

Per-query bounds for `failurePotential`, used by `MLKEMBraid.correctness_error_le`.
The potential and the whole-game argument are described in `MLKEMBraid.Correctness`.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec
open ENNReal

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- `derivedKeyFailure` is at most the indicator that decapsulation does not return the KEM
key. -/
private theorem derivedKeyFailure_le
    [DecidableEq P.K] [DecidableEq P.EpochKey]
    (e : ℕ) (pk : P.PK) (sk : P.SK) (encapsState : P.inc.St) (ct1 : P.inc.C₁) (key : P.K) :
    derivedKeyFailure P e sk ct1
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

/-- The failure potential is at most `1`. -/
private theorem failurePotential_le_one
    [DecidableEq P.K] [DecidableEq P.EpochKey]
    (s : GameState P AuthState) :
    failurePotential P s ≤ 1 := by
  have hrisk : ∀ hdr vec sk, P.inc.decapsFailureProb P.hDet P.hEnc2 hdr vec sk ≤ 1 :=
    fun hdr vec sk => expectedPayoff_le_one _ _ fun _ => by split; split_ifs <;> simp
  have hderived : ∀ e sk ct1 ct2 key, derivedKeyFailure P e sk ct1 ct2 key ≤ 1 := by
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

/-- If `currentEpochFailure` is not `1`, decapsulation at the party's epoch derives the key that
its encapsulator recorded. -/
private theorem decaps_eq_of_currentEpochFailure_ne_one
    [DecidableEq P.K] [DecidableEq P.EpochKey]
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s)
    (hpot : currentEpochFailure P s ≠ 1) (party : Bool) :
    ∀ pk sk encapsState ct1 key,
      (T (if party then s.stA else s.stB).epoch).keypair = some (pk, sk) →
      (T (if party then s.stA else s.stB).epoch).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey P (if party then s.stA else s.stB).epoch pk sk encapsState ct1 =
        some (P.kdfOK key (if party then s.stA else s.stB).epoch) := by
  -- At equal epochs `currentEpochFailure` is `derivedKeyFailure` of the recorded samples. At
  -- different epochs both completed epochs equal the lower epoch, so the decapsulation clause
  -- of `TranscriptConsistent.encaps` applies.
  have hformula := currentEpochFailure_eq_transcript P auth ik T s hT
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
  · have hPA := hPair true
    have hPB := hPair false
    simp only [if_true] at hPA
    simp only [Bool.false_eq_true, ↓reduceIte] at hPB
    have hcross1 := hControl.epochKnowledge.epochA_le
    have hcross2 := hControl.epochKnowledge.epochB_le
    have hA := s.stA.completedEpoch_le_epoch
    have hB := s.stB.completedEpoch_le_epoch
    obtain ⟨e0, hcA, hcB⟩ :
        ∃ e0, s.stA.completedEpoch = e0 ∧ s.stB.completedEpoch = e0 := by
      rcases Nat.lt_or_gt_of_ne hep with hlt | hgt
      · obtain ⟨a, enc, b, dec, hsA, hsB⟩ := hPA.2 (by omega)
        refine ⟨s.stA.epoch, congrArg State.completedEpoch hsA, ?_⟩
        rw [congrArg State.completedEpoch hsB]
        simp [State.completedEpoch, State.epoch]
      · obtain ⟨a, enc, b, dec, hsB, hsA⟩ := hPB.2 (by omega)
        refine ⟨s.stB.epoch, ?_, congrArg State.completedEpoch hsB⟩
        rw [congrArg State.completedEpoch hsA]
        simp [State.completedEpoch, State.epoch]
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

/-- A receive keeps the flag true if decapsulation at its epoch gives the recorded key. -/
private theorem recv_correct_of_decaps_eq
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s) (party : Bool) (n : ℕ)
    (hgood : ∀ pk sk encapsState ct1 key,
      (T (if party then s.stA else s.stB).epoch).keypair = some (pk, sk) →
      (T (if party then s.stA else s.stB).epoch).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey P (if party then s.stA else s.stB).epoch pk sk encapsState ct1 =
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
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hT.correct
    obtain ⟨r, hr, hagree⟩ :=
      (receive_recorded_payload P auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct
        ik T s hT false n msg tsnd hentry).2 hgood
    simp only [Bool.false_eq_true, ↓reduceIte] at hr hagree
    have hrecv : recvSCKA P auth s.stB msg = some (r.outputKey, msg.epoch - 1, r.state) := by
      simp [recvSCKA, hr]
    have hrep : tsnd = msg.epoch - 1 := hControl.recordedReport.1 n msg tsnd hentry
    have hbound : msg.epoch ≤ s.stB.completedEpoch + 1 :=
      (hControl.epochKnowledge.msgA n msg tsnd hentry).2.1
    have htcur : s.tcurB ≤ s.stB.completedEpoch := hControl.epochKnowledge.tcurB_le
    have hkeyB := hControl.epochKnowledge.keyPrefix.prefixB
    have hmax : max s.tcurB (msg.epoch - 1) ≤ s.stB.completedEpoch :=
      max_le htcur (by omega)
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      dsimp only
      simp only [Bool.and_eq_true]
      exact ⟨⟨hT.correct, by simp [hrep]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => (hkeyB t).2 ⟨h0, hle.trans hmax⟩⟩
    · have hstep :=
        (receive_completedEpoch_of_eq_ok P auth s.stB
          hControl.epochKnowledge.keyPrefix.posB msg r hr).2
      simp only [hkey] at hstep
      obtain ⟨htI, -⟩ := hstep
      have hnone : s.keyB tI = none := by
        by_contra hne
        have := ((hkeyB tI).1 hne).2
        omega
      have hpeer : s.keyA tI = some key := hagree tI key hkey
      simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      dsimp only
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨hT.correct, by simp [hrep]⟩, by simp [hnone]⟩, by simp [hpeer]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => ?_⟩
      have hle' := hle.trans hmax
      rw [Function.update_of_ne (by omega)]
      exact (hkeyB t).2 ⟨h0, hle'⟩
  · change z ∈ support ((SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s)
      at hz
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hT.correct
    obtain ⟨r, hr, hagree⟩ :=
      (receive_recorded_payload P auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct
        ik T s hT true n msg tsnd hentry).2 hgood
    simp only [↓reduceIte] at hr hagree
    have hrecv : recvSCKA P auth s.stA msg = some (r.outputKey, msg.epoch - 1, r.state) := by
      simp [recvSCKA, hr]
    have hrep : tsnd = msg.epoch - 1 := hControl.recordedReport.2 n msg tsnd hentry
    have hbound : msg.epoch ≤ s.stA.completedEpoch + 1 :=
      (hControl.epochKnowledge.msgB n msg tsnd hentry).2.1
    have htcur : s.tcurA ≤ s.stA.completedEpoch := hControl.epochKnowledge.tcurA_le
    have hkeyA := hControl.epochKnowledge.keyPrefix.prefixA
    have hmax : max s.tcurA (msg.epoch - 1) ≤ s.stA.completedEpoch :=
      max_le htcur (by omega)
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      dsimp only
      simp only [Bool.and_eq_true]
      exact ⟨⟨hT.correct, by simp [hrep]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => (hkeyA t).2 ⟨h0, hle.trans hmax⟩⟩
    · have hstep :=
        (receive_completedEpoch_of_eq_ok P auth s.stA
          hControl.epochKnowledge.keyPrefix.posA msg r hr).2
      simp only [hkey] at hstep
      obtain ⟨htI, -⟩ := hstep
      have hnone : s.keyA tI = none := by
        by_contra hne
        have := ((hkeyA tI).1 hne).2
        omega
      have hpeer : s.keyB tI = some key := hagree tI key hkey
      simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      dsimp only
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨hT.correct, by simp [hrep]⟩, by simp [hnone]⟩, by simp [hpeer]⟩,
        SCKAScheme.knownPrefix_eq_true fun t h0 hle => ?_⟩
      have hle' := hle.trans hmax
      rw [Function.update_of_ne (by omega)]
      exact (hkeyA t).2 ⟨h0, hle'⟩

/-- A send that samples a key pair has expected potential equal to the KEM correctness error. -/
private theorem expectedPayoff_failurePotential_send_keysUnsampled
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s) (party : Bool) (e : ℕ) (a : AuthState)
    (hst : (if party then s.stA else s.stB) = .keysUnsampled e a) :
    expectedPayoff
        (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)
        (fun z => failurePotential P z.2) =
      P.kem.correctnessError ProbCompRuntime.probComp := by
  -- Every sampled key pair keeps the flag true and gives potential `decapsFailureProb` of that
  -- pair; its average over key generation is the correctness error.
  obtain ⟨b, dec, hpeer⟩ :=
    peer_noHeaderReceived_of_keysUnsampled P auth ik T s hT party e a hst
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
    rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get]
    simp only [scheme, send, hst, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      StateT.run_map, map_pure]
    rw [expectedPayoff_map]
    congr 1
    funext kp
    obtain ⟨pk, sk⟩ := kp
    dsimp only
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
    rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get]
    simp only [scheme, send, hst, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      StateT.run_map, map_pure]
    rw [expectedPayoff_map]
    congr 1
    funext kp
    obtain ⟨pk, sk⟩ := kp
    dsimp only
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
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s) (party : Bool) (e : ℕ) (a : AuthState)
    (hdr : P.inc.PKheader) (dec : DecoderState P.inc.PKvector P.Sym)
    (hst : (if party then s.stA else s.stB) = .headerReceived e a hdr dec) :
    expectedPayoff
        (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)
        (fun z => failurePotential P z.2) ≤
      currentEpochFailure P s := by
  -- `currentEpochFailure` is `decapsFailureProb` of the recorded key pair. Each encapsulation
  -- keeps the flag true and gives potential `derivedKeyFailure`, which is at most the failure of
  -- decapsulation (`derivedKeyFailure_le`).
  obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ :=
    peer_keysSampled_of_headerReceived P auth ik T s hT party e a hdr dec hst
  subst hhdr
  have hcorr : s.correct = true := hT.correct
  have hControl := hT.control
  have hLocal : LocalPayloadInv P auth ik T (if party then s.stA else s.stB) := by
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
  have hΦ : currentEpochFailure P s =
      P.inc.decapsFailureProb P.hDet P.hEnc2 (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
    rw [currentEpochFailure_eq_transcript P auth ik T s hT,
      if_pos (hep.1.trans hep.2.symm)]
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
    rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get]
    simp only [scheme, send, hst, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      StateT.run_map, map_pure]
    rw [expectedPayoff_map]
    refine expectedPayoff_mono _ _ _ fun c => ?_
    obtain ⟨es, ct1, k⟩ := c
    dsimp only
    refine (le_of_eq ?_).trans (derivedKeyFailure_le P e pk sk es ct1 k)
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
    rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get]
    simp only [scheme, send, hst, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      StateT.run_map, map_pure]
    rw [expectedPayoff_map]
    refine expectedPayoff_mono _ _ _ fun c => ?_
    obtain ⟨es, ct1, k⟩ := c
    dsimp only
    refine (le_of_eq ?_).trans (derivedKeyFailure_le P e pk sk es ct1 k)
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
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s) (party : Bool)
    (hsteady : match (if party then s.stA else s.stB) with
      | .keysUnsampled .. => False
      | .headerReceived .. => False
      | _ => True)
    (z : Option (ℕ × Option ℕ × Message P.Sym) × GameState P AuthState)
    (hz : z ∈ support
      (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)) :
    z.2.correct = true ∧ currentEpochFailure P z.2 = currentEpochFailure P s := by
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
    simp only [SCKAScheme.oracleSendB, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hsend : r.sendingEpoch = s.stB.epoch - 1 := by
      rw [send_report_eq_of_mem_support P auth s.stB r hr,
        (send_epoch_fields_of_mem_support P auth s.stB r hr).2.1]
    have hshape : r.outputKey = none ∧
        ∀ s0 : GameState P AuthState,
          s0.stA = s.stA → s0.keyA = s.keyA → s0.keyB = s.keyB → s0.stB = r.state →
            currentEpochFailure P s0 = currentEpochFailure P s := by
      cases hB : s.stB
      all_goals try simp [hB] at hsteady
      all_goals rw [hB] at hr
      all_goals simp only [send, mem_support_pure_iff] at hr
      all_goals subst hr
      all_goals refine ⟨rfl, fun s0 hA0 hkA hkB hB0 => ?_⟩
      all_goals unfold currentEpochFailure pairFailure
      all_goals rw [hA0, hkA, hkB, hB0, hB]
      all_goals first
        | rfl
        | (cases s.stA <;>
            simp [State.controlPosition, State.epoch, EncoderState.nextChunk])
    simp only [hshape.1, StateT.run_map, StateT.run_set, map_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst z
    dsimp only
    refine ⟨?_, hshape.2 _ rfl rfl rfl rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hsend]
    exact ⟨⟨hcorr, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
  · simp only [↓reduceIte] at hsteady hz
    have htcur : s.tcurA ≤ s.stA.epoch - 1 := hControl.tcurA_le_sub_one
    have hkeys : ∀ t, 0 < t → t ≤ s.stA.epoch - 1 → s.keyA t ≠ none := fun t h0 hle =>
      (hControl.epochKnowledge.keyPrefix.prefixA t).2
        ⟨h0, hle.trans s.stA.epoch_sub_one_le_completedEpoch⟩
    simp only [SCKAScheme.oracleSendA, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hsend : r.sendingEpoch = s.stA.epoch - 1 := by
      rw [send_report_eq_of_mem_support P auth s.stA r hr,
        (send_epoch_fields_of_mem_support P auth s.stA r hr).2.1]
    have hshape : r.outputKey = none ∧
        ∀ s0 : GameState P AuthState,
          s0.stB = s.stB → s0.keyA = s.keyA → s0.keyB = s.keyB → s0.stA = r.state →
            currentEpochFailure P s0 = currentEpochFailure P s := by
      cases hA : s.stA
      all_goals try simp [hA] at hsteady
      all_goals rw [hA] at hr
      all_goals simp only [send, mem_support_pure_iff] at hr
      all_goals subst hr
      all_goals refine ⟨rfl, fun s0 hB0 hkA hkB hA0 => ?_⟩
      all_goals unfold currentEpochFailure pairFailure
      all_goals rw [hB0, hkA, hkB, hA0, hA]
      all_goals first
        | rfl
        | (cases s.stB <;>
            simp [State.controlPosition, State.epoch, EncoderState.nextChunk])
    simp only [hshape.1, StateT.run_map, StateT.run_set, map_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst z
    dsimp only
    refine ⟨?_, hshape.2 _ rfl rfl rfl rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hsend]
    exact ⟨⟨hcorr, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩

/-- A successful receive that keeps both epochs does not raise `currentEpochFailure`. -/
private theorem recv_currentEpochFailure_le_of_epochs_eq
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      (((if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)) n).run s))
    (hzc : z.2.correct = true)
    (hepA : z.2.stA.epoch = s.stA.epoch) (hepB : z.2.stB.epoch = s.stB.epoch) :
    currentEpochFailure P z.2 ≤ currentEpochFailure P s := by
  -- Such a receive emits no key and keeps both completed epochs, so the entry transcript still
  -- describes the successor, and `currentEpochFailure_eq_transcript` gives the same value
  -- before and after.
  have hshape : ∀ (st : State P AuthState) (msg : Message P.Sym)
      (r : RecvResult P AuthState), receive P auth st msg = .ok r →
        (r.outputKey = none ∧ r.state.epoch = st.epoch) ∨
          r.state.epoch = st.epoch + 1 := by
    intro st msg r hr
    cases st <;> simp only [receive] at hr
    all_goals repeat' split at hr
    all_goals cases hr
    all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr rfl
  have hTC : ∀ s' : GameState P AuthState,
      s'.correct = true → ControlInv s' → StatePairInv s' →
      s'.stA.epoch = s.stA.epoch → s'.stB.epoch = s.stB.epoch →
      s'.stA.completedEpoch = s.stA.completedEpoch →
      s'.stB.completedEpoch = s.stB.completedEpoch →
      LocalPayloadInv P auth ik T s'.stA → LocalPayloadInv P auth ik T s'.stB →
      s'.msgA = s.msgA → s'.msgB = s.msgB → s'.keyA = s.keyA → s'.keyB = s.keyB →
      TranscriptConsistent P auth ik T s' := by
    intro s' hc hC hP hA hB hcA hcB hLA hLB hmA hmB hkA hkB
    obtain ⟨-, -, -, h0k, h0e, hKeypair, hEncaps, -, -, hMessages, hKeys⟩ := hT
    refine ⟨hc, hC, hP, h0k, h0e, ?_, ?_, hLA, hLB, ?_, ?_⟩
    · intro e pk sk hk
      obtain ⟨h0, hle⟩ := hKeypair e pk sk hk
      have h1 : (if e % 2 = 1 then s'.stA else s'.stB).epoch =
          (if e % 2 = 1 then s.stA else s.stB).epoch := by
        split_ifs <;> assumption
      exact ⟨h0, h1 ▸ hle⟩
    · intro e es ct1 key hc'
      obtain ⟨h0, hle, pk, sk, hkp, hdec⟩ := hEncaps e es ct1 key hc'
      have h1 : (if e % 2 = 1 then s'.stB else s'.stA).completedEpoch =
          (if e % 2 = 1 then s.stB else s.stA).completedEpoch := by
        split_ifs <;> assumption
      have h2 : (if e % 2 = 1 then s'.stA else s'.stB).completedEpoch =
          (if e % 2 = 1 then s.stA else s.stB).completedEpoch := by
        split_ifs <;> assumption
      refine ⟨h0, by rw [h1]; exact hle, pk, sk, hkp, fun h => hdec ?_⟩
      rw [← h2]
      exact h
    · intro party m msg tsnd hmsg
      apply hMessages party m msg tsnd
      cases party
      · simpa [hmB] using hmsg
      · simpa [hmA] using hmsg
    · intro party e
      have hK := hKeys party e
      cases party
      · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
        rw [hkB, hcB]
        exact hK
      · simp only [↓reduceIte] at hK ⊢
        rw [hkA, hcA]
        exact hK
  cases party
  · change z ∈ support ((SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s)
      at hz
    have hCP : ControlInv z.2 ∧ StatePairInv z.2 :=
      correctnessImpl_preserves_controlInv_statePairInv P auth irl sampleInitKey
        (ORecvB (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact le_rfl
    rcases hrecv : recvSCKA P auth s.stB msg with _ | ⟨keyOpt, treport, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      cases hzc
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    subst stB' treport keyOpt
    rcases hshape s.stB msg r hraw with ⟨hnone, hep⟩ | hep
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hnone,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      dsimp only at hzc hCP ⊢
      have hcomp :=
        (receive_completedEpoch_of_eq_ok P auth s.stB
          hT.control.epochKnowledge.keyPrefix.posB msg r hraw).2
      simp only [hnone] at hcomp
      have hLocal := (receive_recorded_payload P auth hHdrCorrect hEkCorrect hCt1Correct
        hCt2Correct ik T s hT false n msg tsnd hentry).1 r hraw
        (fun e key h => by simp [hnone] at h)
      have hTz := hTC _ hzc hCP.1 hCP.2 rfl hep rfl hcomp hT.localA hLocal
        rfl rfl rfl rfl
      refine le_of_eq ?_
      rw [currentEpochFailure_eq_transcript P auth ik T _ hTz,
        currentEpochFailure_eq_transcript P auth ik T s hT]
      simp only [hep]
    · exfalso
      have hzB : z.2.stB = r.state := by
        rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
          simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
            StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz <;>
          subst z <;> rfl
      rw [hzB] at hepB
      omega
  · change z ∈ support ((SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s)
      at hz
    have hCP : ControlInv z.2 ∧ StatePairInv z.2 :=
      correctnessImpl_preserves_controlInv_statePairInv P auth irl sampleInitKey
        (ORecvA (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact le_rfl
    rcases hrecv : recvSCKA P auth s.stA msg with _ | ⟨keyOpt, treport, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      cases hzc
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    subst stA' treport keyOpt
    rcases hshape s.stA msg r hraw with ⟨hnone, hep⟩ | hep
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hnone,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      dsimp only at hzc hCP ⊢
      have hcomp :=
        (receive_completedEpoch_of_eq_ok P auth s.stA
          hT.control.epochKnowledge.keyPrefix.posA msg r hraw).2
      simp only [hnone] at hcomp
      have hLocal := (receive_recorded_payload P auth hHdrCorrect hEkCorrect hCt1Correct
        hCt2Correct ik T s hT true n msg tsnd hentry).1 r hraw
        (fun e key h => by simp [hnone] at h)
      have hTz := hTC _ hzc hCP.1 hCP.2 hep rfl hcomp rfl hLocal hT.localB
        rfl rfl rfl rfl
      refine le_of_eq ?_
      rw [currentEpochFailure_eq_transcript P auth ik T _ hTz,
        currentEpochFailure_eq_transcript P auth ik T s hT]
      simp only [hep]
    · exfalso
      have hzA : z.2.stA = r.state := by
        rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
          simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
            StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz <;>
          subst z <;> rfl
      rw [hzA] at hepA
      omega

/-- A successful receive that changes an epoch leaves `currentEpochFailure` equal to `0`. -/
private theorem recv_currentEpochFailure_eq_zero_of_epoch_ne
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      (((if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)) n).run s))
    (hzc : z.2.correct = true)
    (hchange : z.2.stA.epoch ≠ s.stA.epoch ∨ z.2.stB.epoch ≠ s.stB.epoch) :
    currentEpochFailure P z.2 = 0 := by
  -- Only the receiver moves. Finishing `ct₂` leaves the receiver one epoch ahead of its peer.
  -- A next-epoch message leaves the new generator with no sampled key pair.
  have hshape : ∀ (st : State P AuthState) (msg : Message P.Sym)
      (r : RecvResult P AuthState), receive P auth st msg = .ok r →
        r.state.epoch ≠ st.epoch →
        (∃ a', r.state = .keysUnsampled (st.epoch + 1) a') ∨
          (st.controlPosition.isGenerator = true ∧
            ∃ a' dec', r.state = .noHeaderReceived (st.epoch + 1) a' dec') := by
    intro st msg r hr hne
    cases st <;> simp only [receive] at hr
    all_goals repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact absurd rfl hne
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨rfl, _, _, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T', TranscriptConsistent P auth ik T' z.2 := by
    rcases oracleRecv_preserves_correctnessInv P auth irl sampleInitKey hHdrCorrect
        hEkCorrect hCt1Correct hCt2Correct ik party n s (Or.inr ⟨T, hT⟩) z hz with h | h
    · rw [hzc] at h
      cases h
    · exact h
  rw [currentEpochFailure_eq_transcript P auth ik T' z.2 hT']
  cases party
  · change z ∈ support ((SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s)
      at hz
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · exfalso
      simp only [SCKAScheme.oracleRecvB, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      simp at hchange
    rcases hrecv : recvSCKA P auth s.stB msg with _ | ⟨keyOpt, treport, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      cases hzc
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    subst stB' treport keyOpt
    have hzAB : z.2.stA = s.stA ∧ z.2.stB = r.state := by
      rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
        simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
          StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz <;>
        subst z <;> exact ⟨rfl, rfl⟩
    obtain ⟨hzA, hzB⟩ := hzAB
    have hne : r.state.epoch ≠ s.stB.epoch := by
      rcases hchange with h | h
      · exact absurd (congrArg State.epoch hzA) h
      · rwa [hzB] at h
    have hPB := hT.statePair false
    simp only [Bool.false_eq_true, ↓reduceIte] at hPB
    split_ifs with hzep
    · rcases hshape s.stB msg r hraw hne with ⟨a', hks⟩ | ⟨hgen, a', dec', hnh⟩
      · have hLB := hT'.localB
        rw [hzB, hks] at hLB
        simp only [LocalPayloadInv] at hLB
        obtain ⟨-, hkp0, -⟩ := hLB
        have he : z.2.stA.epoch = s.stB.epoch + 1 :=
          hzep.trans ((congrArg State.epoch hzB).trans (congrArg State.epoch hks))
        simp only [he, hkp0]
      · exfalso
        have h1 : s.stA.epoch = s.stB.epoch + 1 :=
          ((congrArg State.epoch hzA).symm.trans hzep).trans
            ((congrArg State.epoch hzB).trans (congrArg State.epoch hnh))
        obtain ⟨a0, enc0, b0, dec0, hst0, -⟩ := hPB.2 h1
        rw [hst0] at hgen
        simp [State.controlPosition] at hgen
    · rfl
  · change z ∈ support ((SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s)
      at hz
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · exfalso
      simp only [SCKAScheme.oracleRecvA, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      simp at hchange
    rcases hrecv : recvSCKA P auth s.stA msg with _ | ⟨keyOpt, treport, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      cases hzc
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    subst stA' treport keyOpt
    have hzAB : z.2.stA = r.state ∧ z.2.stB = s.stB := by
      rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
        simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
          StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz <;>
        subst z <;> exact ⟨rfl, rfl⟩
    obtain ⟨hzA, hzB⟩ := hzAB
    have hne : r.state.epoch ≠ s.stA.epoch := by
      rcases hchange with h | h
      · rwa [hzA] at h
      · exact absurd (congrArg State.epoch hzB) h
    have hPA := hT.statePair true
    simp only [if_true] at hPA
    split_ifs with hzep
    · rcases hshape s.stA msg r hraw hne with ⟨a', hks⟩ | ⟨hgen, a', dec', hnh⟩
      · have hLA := hT'.localA
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
        obtain ⟨a0, enc0, b0, dec0, hst0, -⟩ := hPA.2 h1
        rw [hst0] at hgen
        simp [State.controlPosition] at hgen
    · rfl

/-- A send query raises the expected potential by at most the KEM correctness error. -/
private theorem expectedPayoff_failurePotential_send_le
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (ik : InitKey)
    (s : GameState P AuthState)
    (hs : CorrectnessInv P auth ik s) (party : Bool) :
    expectedPayoff
        (((if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)) ()).run s)
        (fun z => failurePotential P z.2) ≤
      failurePotential P s + P.kem.correctnessError ProbCompRuntime.probComp := by
  rcases hs with hsf | ⟨T, hT⟩
  · have h1 : failurePotential P s = 1 := by simp [failurePotential, hsf]
    rw [h1]
    refine le_trans ?_ le_self_add
    exact expectedPayoff_le_one _ _ fun z => failurePotential_le_one P z.2
  have hF : failurePotential P s = currentEpochFailure P s := by
    simp [failurePotential, hT.correct]
  cases hst : (if party then s.stA else s.stB) with
  | keysUnsampled e a =>
      rw [expectedPayoff_failurePotential_send_keysUnsampled P auth irl sampleInitKey ik T s hT
        party e a hst]
      exact le_add_self
  | headerReceived e a hdr dec =>
      rw [hF]
      exact (expectedPayoff_failurePotential_send_headerReceived_le P auth irl sampleInitKey ik T s
        hT party e a hdr dec hst).trans le_self_add
  | _ =>
      refine le_trans ?_ le_self_add
      refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
        fun z hz => ?_
      obtain ⟨hzc, hpot⟩ :=
        send_correct_and_currentEpochFailure_eq P auth irl sampleInitKey ik T s hT party
        (by rw [hst]; trivial) z hz
      simp [failurePotential, hzc, hpot, hT.correct]

/-- A receive query does not raise the expected potential. -/
private theorem expectedPayoff_failurePotential_recv_le
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey)
    (s : GameState P AuthState)
    (hs : CorrectnessInv P auth ik s) (party : Bool) (n : ℕ) :
    expectedPayoff
        (((if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
          else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)) n).run s)
        (fun z => failurePotential P z.2) ≤
      failurePotential P s := by
  rcases hs with hsf | ⟨T, hT⟩
  · have h1 : failurePotential P s = 1 := by simp [failurePotential, hsf]
    rw [h1]
    exact expectedPayoff_le_one _ _ fun z => failurePotential_le_one P z.2
  have hF : failurePotential P s = currentEpochFailure P s := by
    simp [failurePotential, hT.correct]
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
    fun z hz => ?_
  rw [hF]
  cases hzc : z.2.correct
  · -- A receive clears the flag only if decapsulation at the receiver's epoch does not return
    -- the recorded key.
    have h : currentEpochFailure P s = 1 := by
      by_contra hne
      simpa [hzc] using recv_correct_of_decaps_eq P auth irl sampleInitKey hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik T s hT party n
        (decaps_eq_of_currentEpochFailure_ne_one P auth ik T s hT hne party) z hz
    simp [failurePotential, hzc, h]
  · simp only [failurePotential, hzc, if_true]
    by_cases h : z.2.stA.epoch = s.stA.epoch ∧ z.2.stB.epoch = s.stB.epoch
    · exact recv_currentEpochFailure_le_of_epochs_eq P auth irl sampleInitKey hHdrCorrect
        hEkCorrect hCt1Correct hCt2Correct ik T s hT party n z hz hzc h.1 h.2
    · rw [recv_currentEpochFailure_eq_zero_of_epoch_ne P auth irl sampleInitKey hHdrCorrect
        hEkCorrect hCt1Correct hCt2Correct ik T s hT party n z hz hzc (not_and_or.mp h)]
      exact zero_le

/-- One query of the correctness game raises the expected failure potential by at most the
KEM correctness error for a send query, and not at all for other queries. The state must
satisfy the correctness invariant, and the four erasure codes must be correct. -/
theorem expectedPayoff_failurePotential_query_le
    [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Domain)
    (s : GameState P AuthState)
    (hs : CorrectnessInv P auth ik s) :
    expectedPayoff
        ((SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey) t).run s)
        (fun z => failurePotential P z.2) ≤
      failurePotential P s +
        if SCKAScheme.isSendQuery (Rho := Message P.Sym) t
        then P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
  match t with
  | SCKAScheme.sckaCorrectnessSpec.OUnif n =>
      rw [if_neg (by simp [SCKAScheme.isSendQuery]), add_zero]
      refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
        fun z hz => ?_
      exact le_of_eq (congrArg (failurePotential P)
        (SCKAScheme.oracleUnif_preservesInv (· = s) n s rfl z hz))
  | SCKAScheme.sckaCorrectnessSpec.OSendA =>
      rw [if_pos (by simp [SCKAScheme.isSendQuery])]
      exact expectedPayoff_failurePotential_send_le P auth irl sampleInitKey ik s hs true
  | SCKAScheme.sckaCorrectnessSpec.OSendB =>
      rw [if_pos (by simp [SCKAScheme.isSendQuery])]
      exact expectedPayoff_failurePotential_send_le P auth irl sampleInitKey ik s hs false
  | SCKAScheme.sckaCorrectnessSpec.ORecvA n =>
      rw [if_neg (by simp [SCKAScheme.isSendQuery]), add_zero]
      exact expectedPayoff_failurePotential_recv_le P auth irl sampleInitKey hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik s hs true n
  | SCKAScheme.sckaCorrectnessSpec.ORecvB n =>
      rw [if_neg (by simp [SCKAScheme.isSendQuery]), add_zero]
      exact expectedPayoff_failurePotential_recv_le P auth irl sampleInitKey hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik s hs false n

end MLKEMBraid
