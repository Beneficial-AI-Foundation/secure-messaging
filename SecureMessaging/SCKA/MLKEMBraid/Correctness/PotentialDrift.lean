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

Let `Π := scheme P auth irl sampleInitKey` be a Braid SCKA scheme and let
`ε := P.kem.correctnessError ProbCompRuntime.probComp`. Put `V(s) := failurePotential s`.

Assume the four erasure codes are correct. For every initial key `ik`, state `s` satisfying
`CorrectnessInv auth ik s`, and query `t`, `expectedPayoff_failurePotential_query_le` gives

```
E[V(s')] ≤ V(s) + if SCKAScheme.isSendQuery t then ε else 0.
```

The expectation is over the successor state `s'` of the oracle answering `t` from `s`.
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
/-- When `currentEpochFailure s ≠ 1`, the recorded samples at either party's epoch decapsulate to
the recorded derived key. -/
private theorem decaps_eq_of_currentEpochFailure_ne_one
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s)
    (hpot : currentEpochFailure s ≠ 1) (party : Bool) :
    ∀ pk sk encapsState ct1 key,
      (T (s.stateAt party).epoch).keypair = some (pk, sk) →
      (T (s.stateAt party).epoch).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey (s.stateAt party).epoch pk sk encapsState ct1 =
        some (P.kdfOK key (s.stateAt party).epoch) := by
  -- At equal epochs `currentEpochFailure` is `derivedKeyFailure` of the recorded samples. At
  -- different epochs both completed epochs equal the lower epoch, so the decapsulation clause
  -- of `TranscriptConsistent.encaps` applies.
  have hformula := currentEpochFailure_eq_transcript auth hT
  obtain ⟨-, hControl, hPair, -, -, -, hEncaps, -, -, -, -⟩ := hT
  intro pk sk es ct1 key hkp hc
  by_cases hep : s.stA.epoch = s.stB.epoch
  · have he : (s.stateAt party).epoch = s.stA.epoch := by
      cases party
      · exact hep.symm
      · rfl
    rw [he] at hkp hc ⊢
    rw [if_pos hep] at hformula
    simp only [EpochTranscript.failurePotential, hkp, hc] at hformula
    rw [hformula] at hpot
    unfold derivedKeyFailure at hpot
    split_ifs at hpot with hd
    · exact hd
    · exact absurd rfl hpot
  · have hcrossA : s.stA.epoch ≤ s.stB.completedEpoch + 1 :=
      hControl.epochKnowledge.epoch_le true
    have hcrossB : s.stB.epoch ≤ s.stA.completedEpoch + 1 :=
      hControl.epochKnowledge.epoch_le false
    have hPairA : PairInv s.stA s.stB := hPair.pair true
    have hPairB : PairInv s.stB s.stA := hPair.pair false
    have hA := s.stA.completedEpoch_le_epoch
    have hB := s.stB.completedEpoch_le_epoch
    obtain ⟨e0, hcA, hcB⟩ :
        ∃ e0, s.stA.completedEpoch = e0 ∧ s.stB.completedEpoch = e0 := by
      rcases Nat.lt_or_gt_of_ne hep with hlt | hgt
      · obtain ⟨hposA, hposB⟩ := hPairA.2 (by omega)
        refine ⟨s.stA.epoch, ?_, ?_⟩
        · rw [s.stA.completedEpoch_eq, hposA]
          simp
        · rw [s.stB.completedEpoch_eq, hposB]
          simp
          omega
      · obtain ⟨hposB, hposA⟩ := hPairB.2 (by omega)
        refine ⟨s.stB.epoch, ?_, ?_⟩
        · rw [s.stA.completedEpoch_eq, hposA]
          simp
          omega
        · rw [s.stB.completedEpoch_eq, hposB]
          simp
    generalize (s.stateAt party).epoch = e at hkp hc ⊢
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
/-- Correct decapsulation of the receiver's recorded samples keeps the correctness flag true on
supported receive outcomes. -/
private theorem recv_correct_of_decaps_eq
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (hgood : ∀ pk sk encapsState ct1 key,
      (T (s.stateAt party).epoch).keypair = some (pk, sk) →
      (T (s.stateAt party).epoch).encaps1 = some (encapsState, ct1, key) →
      decapsEpochKey (s.stateAt party).epoch pk sk encapsState ct1 =
        some (P.kdfOK key (s.stateAt party).epoch))
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      ((oracleRecv auth irl sampleInitKey party n).run s)) :
    z.2.correct = true := by
  have hControl := hT.control
  rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
    ⟨-, rfl⟩ | ⟨msg, tsnd, err, hentry, hraw, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
  · exact hT.correct
  all_goals
    obtain ⟨r₀, hr₀, hagree⟩ :=
      (receive_recorded_payload auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct hT party n
        msg tsnd hentry).2 hgood
  · rw [hr₀] at hraw
    cases hraw
  rw [Except.ok.inj (hr₀.symm.trans hraw)] at hagree
  have hrep := hControl.recordedReport.report (!party) n msg tsnd hentry
  have hbound := (hControl.epochKnowledge.msgs (!party) n msg tsnd hentry).2.1
  simp only [Bool.not_not] at hbound
  have htcur := hControl.epochKnowledge.tcur_le party
  have hprefix := hControl.epochKnowledge.keyPrefix.keys party
  have hmax : max (s.tcurAt party) (msg.epoch - 1) ≤ (s.stateAt party).completedEpoch := by omega
  have hknown := SCKAScheme.knownPrefix_eq_true
    fun t h0 hle => (hprefix t).2 ⟨h0, hle.trans hmax⟩
  rw [recvUpdate_correct]
  rcases hkey : r.outputKey with _ | ⟨tI, key⟩
  · simp only [Bool.and_eq_true]
    exact ⟨⟨hT.correct, by simp [hrep]⟩, hknown⟩
  · have hpos := hControl.epochKnowledge.keyPrefix.pos party
    have hstep := ((ReceiveEdge.of_eq_ok auth hraw).completedEpoch hpos).2
    simp only [hkey] at hstep
    obtain ⟨htI, -⟩ := hstep
    have hnone : s.keysAt party tI = none := by
      by_contra hne
      have := ((hprefix tI).1 hne).2
      omega
    have hpeer := hagree tI key hkey
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨hT.correct, by simp [hrep]⟩, by simp [hnone]⟩, by simp [hpeer]⟩,
      SCKAScheme.knownPrefix_update_some hknown tI key⟩

omit [DecidableEq P.Sym] in
/-- If `party` is key-generating and its peer is not, `currentEpochFailure` is `pairFailure` of
their states at equal epochs and `0` otherwise. -/
private theorem currentEpochFailure_eq_pair
    (s : GameState P AuthState) (party : Bool)
    (hgen : (s.stateAt party).controlPosition.isGenerator = true)
    (henc : (s.stateAt (!party)).controlPosition.isGenerator = false) :
    currentEpochFailure s =
      if (s.stateAt party).epoch ≠ (s.stateAt (!party)).epoch then 0
      else pairFailure (s.stateAt party) (s.stateAt (!party)) (s.keysAt (!party)) := by
  cases party
  · simp only [GameState.stateAt, GameState.keysAt, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] at henc ⊢
    simp only [currentEpochFailure, henc, Bool.false_eq_true, ↓reduceIte]
  · simp only [GameState.stateAt, GameState.keysAt, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hgen ⊢
    simp only [currentEpochFailure, hgen, ↓reduceIte]

/-- A send from `keysUnsampled` has expected successor potential equal to the KEM correctness error.
-/
private theorem expectedPayoff_failurePotential_send_keysUnsampled
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) {e : ℕ} {a : AuthState}
    (hst : (s.stateAt party) = .keysUnsampled e a) :
    expectedPayoff
        ((oracleSend auth irl sampleInitKey party ()).run s)
        (fun z => failurePotential z.2) =
      P.kem.correctnessError ProbCompRuntime.probComp := by
  obtain ⟨b, dec, hpeer⟩ := peer_noHeaderReceived_of_keysUnsampled auth hT party hst
  obtain ⟨htcur, hkeys⟩ := hT.control.send_prefix party
  rw [hst] at htcur hkeys
  rw [← P.inc.expectedPayoff_keygen_decapsFailureProb P.hDet P.hEnc2,
    oracleSend_run_eq auth irl sampleInitKey, expectedPayoff_map, hst,
    send_keysUnsampled_eq, expectedPayoff_map]
  congr 1
  funext kp
  obtain ⟨pk, sk⟩ := kp
  dsimp only [Function.comp_def]
  have hflag : (s.correct && decide (s.tcurAt party ≤ e - 1) &&
      SCKAScheme.knownPrefix (s.keysAt party) (e - 1)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hT.correct, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
  simp only [failurePotential, sendUpdate_correct, hflag, if_true]
  rw [currentEpochFailure_eq_pair _ party]
  · simp [hpeer, pairFailure, State.epoch, EncoderState.nextChunk, EncoderState.init]
  · simp [State.controlPosition]
  · simp [hpeer, State.controlPosition]

/-- A send from `headerReceived` does not raise the expected potential. -/
private theorem expectedPayoff_failurePotential_send_headerReceived_le
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) {e : ℕ} {a : AuthState}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : (s.stateAt party) = .headerReceived e a hdr dec) :
    expectedPayoff
        ((oracleSend auth irl sampleInitKey party ()).run s)
        (fun z => failurePotential z.2) ≤
      currentEpochFailure s := by
  obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ := peer_keysSampled_of_headerReceived auth hT party hst
  subst hhdr
  have hc0 : (T e).encaps1 = none := by
    have hLocal := hT.local auth party
    rw [hst] at hLocal
    exact hLocal.2.1
  have hΦ : currentEpochFailure s =
      P.inc.decapsFailureProb P.hDet P.hEnc2 (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
    rw [currentEpochFailure_eq_transcript_party auth hT party]
    simp only [hst, hpeer, State.epoch, EpochTranscript.failurePotential, hkpT, hc0, if_true]
  obtain ⟨htcur, hkeys⟩ := hT.control.send_prefix party
  rw [hst] at htcur hkeys
  have hnone : ∀ who, s.keysAt who e = none := by
    intro who
    have hprefix := hT.control.epochKnowledge.keyPrefix.keys who e
    by_contra hne
    obtain ⟨hpos, hbound⟩ := hprefix.1 hne
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst] at hbound
      simp only [State.completedEpoch, State.epoch] at hbound
      omega
    · rw [hpeer] at hbound
      simp only [State.completedEpoch, State.epoch] at hbound
      omega
  rw [hΦ]
  unfold KEMScheme.IncrementalStructure.decapsFailureProb
  rw [oracleSend_run_eq auth irl sampleInitKey, expectedPayoff_map, hst,
    send_headerReceived_eq, expectedPayoff_map]
  refine expectedPayoff_mono _ _ _ fun c => ?_
  obtain ⟨es, ct1, k⟩ := c
  dsimp only [Function.comp_def]
  have hflag : (s.correct && decide (s.tcurAt party ≤ e - 1) &&
      (s.keysAt party e).isNone &&
      ((s.keysAt (!party) e).isNone || s.keysAt (!party) e == some (P.kdfOK k e)) &&
      SCKAScheme.knownPrefix
        (Function.update (s.keysAt party) e (some (P.kdfOK k e))) (e - 1)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hT.correct, htcur⟩, by simp [hnone]⟩, by simp [hnone]⟩,
      SCKAScheme.knownPrefix_update_some (SCKAScheme.knownPrefix_eq_true hkeys) e (P.kdfOK k e)⟩
  refine le_trans (le_of_eq ?_) (derivedKeyFailure_le e pk sk es ct1 k)
  simp only [failurePotential, sendUpdate_correct, hflag, if_true]
  rw [currentEpochFailure_eq_pair _ (!party)]
  · simp [hpeer, pairFailure, State.epoch]
  · simp [hpeer, State.controlPosition]
  · simp [State.controlPosition]

/-- A send without sampling keeps the correctness flag true and `currentEpochFailure` unchanged. -/
private theorem send_correct_and_currentEpochFailure_eq
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool)
    (hsteady : (s.stateAt party).SendsNoSample)
    (z : Option (ℕ × Option ℕ × Message P.Sym) × GameState P AuthState)
    (hz : z ∈ support
      ((oracleSend auth irl sampleInitKey party ()).run s)) :
    z.2.correct = true ∧ currentEpochFailure z.2 = currentEpochFailure s := by
  obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSend_run_iff auth irl sampleInitKey s party z).mp hz
  have hedge := (mem_support_send_iff auth).mp hr
  obtain ⟨htcur, hkeys⟩ := hT.control.send_prefix party
  have hkey : r.outputKey = none := hedge.outputKey_eq_none fun e a hdr dec hst => by
    rw [hst] at hsteady
    exact hsteady
  have hzc : (sendUpdate s party r).correct = true := by
    rw [sendUpdate_correct, hkey, hedge.sendingEpoch_eq]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hT.correct, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
  refine ⟨hzc, ?_⟩
  have hCP := oracleSend_preserves_controlInv_statePairInv auth irl sampleInitKey party
    () s ⟨hT.control, hT.statePair⟩ _
    ((mem_support_oracleSend_run_iff auth irl sampleInitKey s party _).2 ⟨r, hr, rfl⟩)
  have hup := sendUpdate_eq_successor_of_correct s party r hT.correct hzc
  rw [hup] at hCP ⊢
  have hTz := send_existing_transcript auth hT party hr hsteady hCP
  rw [currentEpochFailure_eq_transcript auth hTz, currentEpochFailure_eq_transcript auth hT]
  have hEpoch := fun who => epoch_stateAt_sendSuccessor s party who r hedge.epoch_eq.1
  rw [show (sendSuccessor s party r).stA.epoch = s.stA.epoch from hEpoch true,
    show (sendSuccessor s party r).stB.epoch = s.stB.epoch from hEpoch false]

/-- With a true successor flag and unchanged epochs, a supported receive does not increase
`currentEpochFailure`. -/
private theorem recv_currentEpochFailure_le_of_epochs_eq
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      ((oracleRecv auth irl sampleInitKey party n).run s))
    (hzc : z.2.correct = true)
    (hepA : z.2.stA.epoch = s.stA.epoch) (hepB : z.2.stB.epoch = s.stB.epoch) :
    currentEpochFailure z.2 ≤ currentEpochFailure s := by
  have hTz := oracleRecv_preserves_transcriptConsistent auth irl sampleInitKey hHdrCorrect
    hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc
  rw [currentEpochFailure_eq_transcript auth hTz, currentEpochFailure_eq_transcript auth hT,
    hepA, hepB]

/-- With a true successor flag, a supported receive changing a party's epoch leaves
`currentEpochFailure = 0`. -/
private theorem recv_currentEpochFailure_eq_zero_of_epoch_ne
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      ((oracleRecv auth irl sampleInitKey party n).run s))
    (hzc : z.2.correct = true)
    (hchange : z.2.stA.epoch ≠ s.stA.epoch ∨ z.2.stB.epoch ≠ s.stB.epoch) :
    currentEpochFailure z.2 = 0 := by
  have hTz := oracleRecv_preserves_transcriptConsistent auth irl sampleInitKey hHdrCorrect
    hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc
  rw [currentEpochFailure_eq_transcript_party auth hTz party]
  rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
    ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, hzeq⟩
  · simp at hchange
  · cases hzc
  have hedge := ReceiveEdge.of_eq_ok auth hraw
  have hzLocal : z.2.stateAt party = r.state := by rw [hzeq]; simp
  have hzPeer : z.2.stateAt (!party) = s.stateAt (!party) := by rw [hzeq]; simp
  have hne : r.state.epoch ≠ (s.stateAt party).epoch := by
    intro heq
    have hEpoch : ∀ who, (z.2.stateAt who).epoch = (s.stateAt who).epoch := by
      intro who
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hzLocal]; exact heq
      · rw [hzPeer]
    rcases hchange with h | h
    · exact h (hEpoch true)
    · exact h (hEpoch false)
  split_ifs with hzep
  · rcases hedge.advance hne with ⟨-, -, a', hks⟩ | ⟨hgen, -, -, a', dec', hnh⟩
    · -- The new generator has no sampled key pair.
      have hLocal := hTz.local auth party
      rw [hzLocal, hks] at hLocal
      simp only [LocalPayloadInv] at hLocal
      obtain ⟨-, hkp0, -⟩ := hLocal
      have he : (z.2.stateAt party).epoch = (s.stateAt party).epoch + 1 :=
        (congrArg State.epoch hzLocal).trans (congrArg State.epoch hks)
      simp only [he, EpochTranscript.failurePotential, hkp0]
    · -- A generator one epoch behind its peer contradicts the pair invariant.
      exfalso
      have h1 : (s.stateAt (!party)).epoch = (s.stateAt party).epoch + 1 :=
        ((congrArg State.epoch hzPeer).symm.trans hzep.symm).trans
          ((congrArg State.epoch hzLocal).trans (congrArg State.epoch hnh))
      have hPair := hT.statePair.pair party
      rw [(hPair.2 h1).1] at hgen
      simp at hgen
  · rfl

/-- Either party's send raises expected `failurePotential` by at most the KEM correctness error. -/
private theorem expectedPayoff_failurePotential_send_le
    (ik : InitKey) (s : GameState P AuthState)
    (hs : CorrectnessInv auth ik s) (party : Bool) :
    expectedPayoff
        ((oracleSend auth irl sampleInitKey party ()).run s)
        (fun z => failurePotential z.2) ≤
      failurePotential s + P.kem.correctnessError ProbCompRuntime.probComp := by
  rcases hs with hsf | ⟨T, hT⟩
  · have h1 : failurePotential s = 1 := by simp [failurePotential, hsf]
    rw [h1]
    refine le_trans ?_ le_self_add
    exact expectedPayoff_le_one _ _ fun z => failurePotential_le_one z.2
  have hF : failurePotential s = currentEpochFailure s := by
    simp [failurePotential, hT.correct]
  cases hst : (s.stateAt party) with
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

/-- With correct erasure codes, either party's receive does not raise expected `failurePotential`.
-/
private theorem expectedPayoff_failurePotential_recv_le
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (s : GameState P AuthState)
    (hs : CorrectnessInv auth ik s) (party : Bool) (n : ℕ) :
    expectedPayoff
        ((oracleRecv auth irl sampleInitKey party n).run s)
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
