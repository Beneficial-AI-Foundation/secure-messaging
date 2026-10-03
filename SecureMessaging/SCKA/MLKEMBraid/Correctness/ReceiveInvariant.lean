/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.RecordedPayload

/-!
# Receives preserve the correctness invariant

A successful receive of a recorded message keeps the game state consistent with the same
transcript when any output key agrees with the peer's recorded key for that epoch
(`receive_preserves_transcriptConsistent`). A refusal or a key disagreement clears the correctness
flag. If the successor flag stays true, the receive oracle preserves the same transcript
(`oracleRecv_preserves_transcriptConsistent`), and hence preserves `CorrectnessInv`
(`oracleRecv_preserves_correctnessInv`).
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable {P : Parameters ProbComp} [DecidableEq P.Sym] {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- A successful receive of a message recorded by the peer, whose output key agrees with the
peer's recorded key, keeps the game state consistent with the same transcript. The successor
state `s'` carries the receiver's new state, current epoch and key table but the old correctness
flag; it is required to satisfy the control and pair invariants. -/
theorem receive_preserves_transcriptConsistent
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (s.stateAt party) msg = .ok r)
    (hOutputs : ∀ e key, r.outputKey = some (e, key) →
      s.keysAt (!party) e = some key) :
    let s' := if party then
      { s with
        stA := r.state,
        tcurA := max s.tcurA (msg.epoch - 1),
        keyA := (match r.outputKey with
          | none => s.keyA
          | some (e, key) => Function.update s.keyA e (some key)) }
    else
      { s with
        stB := r.state,
        tcurB := max s.tcurB (msg.epoch - 1),
        keyB := (match r.outputKey with
          | none => s.keyB
          | some (e, key) => Function.update s.keyB e (some key)) }
    (ControlInv s' ∧ StatePairInv s') → TranscriptConsistent auth ik T s' := by
  -- The receiver keeps its local payload invariant, never lowers its epoch or completed
  -- epoch, and outputs only the transcript key of its next completed epoch.
  have hLocalNew : LocalPayloadInv auth ik T r.state :=
    (receive_recorded_payload auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct hT
      party n msg tsnd hmsg).1 r hr hOutputs
  have hedge := ReceiveEdge.of_eq_ok auth hr
  have hmono : (s.stateAt party).epoch ≤ r.state.epoch := hedge.epoch_le.1
  have hpos := hT.control.epochKnowledge.keyPrefix.pos party
  have hstep := (hedge.completedEpoch hpos).2
  have hcomp : (r.outputKey = none ∧
        r.state.completedEpoch = (s.stateAt party).completedEpoch) ∨
      ∃ t key, r.outputKey = some (t, key) ∧
        t = (s.stateAt party).completedEpoch + 1 ∧
        r.state.completedEpoch = t := by
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey] at hstep
        exact Or.inl ⟨rfl, hstep⟩
    | some out =>
        rcases out with ⟨t, key⟩
        simp only [hkey] at hstep
        exact Or.inr ⟨t, key, rfl, hstep⟩
  have hkeyFact : ∀ t key, r.outputKey = some (t, key) →
      ∃ pk sk encapsState ct1 k, (T t).keypair = some (pk, sk) ∧
        (T t).encaps1 = some (encapsState, ct1, k) ∧
        decapsEpochKey t pk sk encapsState ct1 = some (P.kdfOK k t) ∧
        key = P.kdfOK k t := by
    intro t key hout
    obtain ⟨-, -, pk, sk, encapsState, ct1, k, hkp, hc, hdec, hpeer⟩ :=
      receive_recorded_output auth hCt2Correct hT party n msg tsnd hmsg r hr t key hout
    have hkey : key = P.kdfOK k t := Option.some.inj ((hOutputs t key hout).symm.trans hpeer)
    subst hkey
    exact ⟨pk, sk, encapsState, ct1, k, hkp, hc, hdec, rfl⟩
  obtain ⟨hcorr, -, -, h0k, h0e, hKeypair, hEncaps, hLocalA, hLocalB, hMessages, hKeys⟩ := hT
  cases party
  · simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hmono hcomp ⊢
    have hcompMono : s.stB.completedEpoch ≤ r.state.completedEpoch := by
      rcases hcomp with ⟨-, h⟩ | ⟨t, key, -, ht, h⟩ <;> omega
    rintro ⟨hC', hP'⟩
    refine ⟨hcorr, hC', hP', h0k, h0e, ?_, ?_, hLocalA, hLocalNew, hMessages, ?_⟩
    · intro e pk sk hk
      obtain ⟨h0, hle⟩ := hKeypair e pk sk hk
      refine ⟨h0, ?_⟩
      by_cases hpar : e % 2 = 1
      · rw [if_pos hpar] at hle ⊢
        exact hle
      · rw [if_neg hpar] at hle ⊢
        exact hle.trans hmono
    · intro e encapsState ct1 key hc
      obtain ⟨h0, hle, pk, sk, hkp, hdec⟩ := hEncaps e encapsState ct1 key hc
      refine ⟨h0, ?_, pk, sk, hkp, fun hle' => ?_⟩
      · by_cases hpar : e % 2 = 1
        · rw [if_pos hpar] at hle ⊢
          exact hle.trans hcompMono
        · rw [if_neg hpar] at hle ⊢
          exact hle
      · by_cases hpar : e % 2 = 1
        · rw [if_pos hpar] at hdec hle'
          exact hdec hle'
        · rw [if_neg hpar] at hdec hle'
          rcases hcomp with ⟨-, hceq⟩ | ⟨t, k', hkey, ht, hceq⟩
          · rw [hceq] at hle'
            exact hdec hle'
          · by_cases het : e = t
            · subst het
              obtain ⟨pk', sk', es', ct1', k'', hkp', hc', hdec', -⟩ := hkeyFact e k' hkey
              rw [hkp] at hkp'
              rw [hc] at hc'
              cases hkp'
              cases hc'
              exact hdec'
            · rw [hceq] at hle'
              exact hdec (by omega)
    · intro party' e
      have hK := hKeys party' e
      cases party'
      · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
        rcases hcomp with ⟨hnone, hceq⟩ | ⟨t, key, hkey, ht, hceq⟩
        · rw [hnone, hceq]
          exact hK
        · rw [hkey, hceq]
          change Function.update s.keyB t (some key) e = _
          by_cases het : e = t
          · subst het
            obtain ⟨-, -, es', ct1', k', -, hc', -, hk'⟩ := hkeyFact e key hkey
            rw [Function.update_self, if_pos ⟨by omega, le_refl e⟩, hc']
            exact congrArg some hk'
          · rw [Function.update_of_ne het, hK]
            by_cases h1 : 0 < e ∧ e ≤ s.stB.completedEpoch
            · rw [if_pos h1, if_pos (by omega)]
            · rw [if_neg h1, if_neg (by omega)]
      · simp only [↓reduceIte] at hK ⊢
        exact hK
  · simp only [GameState.stateAt, ↓reduceIte] at hmono hcomp ⊢
    have hcompMono : s.stA.completedEpoch ≤ r.state.completedEpoch := by
      rcases hcomp with ⟨-, h⟩ | ⟨t, key, -, ht, h⟩ <;> omega
    rintro ⟨hC', hP'⟩
    refine ⟨hcorr, hC', hP', h0k, h0e, ?_, ?_, hLocalNew, hLocalB, hMessages, ?_⟩
    · intro e pk sk hk
      obtain ⟨h0, hle⟩ := hKeypair e pk sk hk
      refine ⟨h0, ?_⟩
      by_cases hpar : e % 2 = 1
      · rw [if_pos hpar] at hle ⊢
        exact hle.trans hmono
      · rw [if_neg hpar] at hle ⊢
        exact hle
    · intro e encapsState ct1 key hc
      obtain ⟨h0, hle, pk, sk, hkp, hdec⟩ := hEncaps e encapsState ct1 key hc
      refine ⟨h0, ?_, pk, sk, hkp, fun hle' => ?_⟩
      · by_cases hpar : e % 2 = 1
        · rw [if_pos hpar] at hle ⊢
          exact hle
        · rw [if_neg hpar] at hle ⊢
          exact hle.trans hcompMono
      · by_cases hpar : e % 2 = 1
        · rw [if_pos hpar] at hdec hle'
          rcases hcomp with ⟨-, hceq⟩ | ⟨t, k', hkey, ht, hceq⟩
          · rw [hceq] at hle'
            exact hdec hle'
          · by_cases het : e = t
            · subst het
              obtain ⟨pk', sk', es', ct1', k'', hkp', hc', hdec', -⟩ := hkeyFact e k' hkey
              rw [hkp] at hkp'
              rw [hc] at hc'
              cases hkp'
              cases hc'
              exact hdec'
            · rw [hceq] at hle'
              exact hdec (by omega)
        · rw [if_neg hpar] at hdec hle'
          exact hdec hle'
    · intro party' e
      have hK := hKeys party' e
      cases party'
      · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
        exact hK
      · simp only [↓reduceIte] at hK ⊢
        rcases hcomp with ⟨hnone, hceq⟩ | ⟨t, key, hkey, ht, hceq⟩
        · rw [hnone, hceq]
          exact hK
        · rw [hkey, hceq]
          change Function.update s.keyA t (some key) e = _
          by_cases het : e = t
          · subst het
            obtain ⟨-, -, es', ct1', k', -, hc', -, hk'⟩ := hkeyFact e key hkey
            rw [Function.update_self, if_pos ⟨by omega, le_refl e⟩, hc']
            exact congrArg some hk'
          · rw [Function.update_of_ne het, hK]
            by_cases h1 : 0 < e ∧ e ≤ s.stA.completedEpoch
            · rw [if_pos h1, if_pos (by omega)]
            · rw [if_neg h1, if_neg (by omega)]

variable [DecidableEq P.EpochKey]
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

/-- A supported receive whose successor correctness flag is true keeps the game state
consistent with the same transcript. -/
theorem oracleRecv_preserves_transcriptConsistent
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      ((oracleRecv auth irl sampleInitKey party n).run s))
    (hzc : z.2.correct = true) :
    TranscriptConsistent auth ik T z.2 := by
  -- A missing record keeps the state, and a refusal clears the flag. If a successful receive
  -- leaves the flag true, the output key agrees with the peer's key for its epoch, so
  -- `receive_preserves_transcriptConsistent` keeps the new state consistent with the same
  -- transcript.
  cases party
  · have hCPz : ControlInv z.2 ∧ StatePairInv z.2 :=
      correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (ORecvB (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hT
    · cases hzc
    have hagree : ∀ e key, r.outputKey = some (e, key) → s.keyA e = some key := by
      intro e key hkey
      obtain ⟨-, -, _, _, _, _, _, -, -, -, hpeer⟩ :=
        receive_recorded_output auth hCt2Correct hT false n msg tsnd hentry r hraw e key hkey
      simp only [GameState.keysAt, Bool.not_false, ↓reduceIte] at hpeer
      simp only [SCKAScheme.recvBUpdate, hkey, Bool.and_eq_true, Bool.or_eq_true] at hzc
      obtain ⟨⟨-, hcons⟩, -⟩ := hzc
      rcases hcons with hnone | hbeq
      · simp [hpeer] at hnone
      · exact beq_iff_eq.mp hbeq
    have h := receive_preserves_transcriptConsistent auth hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct hT false n msg tsnd hentry r hraw hagree
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp only [SCKAScheme.recvBUpdate, hkey] at hzc hCPz ⊢
      rw [hzc] at hCPz ⊢
      simp only [hkey, hT.correct] at h
      exact h hCPz
  · have hCPz : ControlInv z.2 ∧ StatePairInv z.2 :=
      correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (ORecvA (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hT
    · cases hzc
    have hagree : ∀ e key, r.outputKey = some (e, key) → s.keyB e = some key := by
      intro e key hkey
      obtain ⟨-, -, _, _, _, _, _, -, -, -, hpeer⟩ :=
        receive_recorded_output auth hCt2Correct hT true n msg tsnd hentry r hraw e key hkey
      simp only [GameState.keysAt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpeer
      simp only [SCKAScheme.recvAUpdate, hkey, Bool.and_eq_true, Bool.or_eq_true] at hzc
      obtain ⟨⟨-, hcons⟩, -⟩ := hzc
      rcases hcons with hnone | hbeq
      · simp [hpeer] at hnone
      · exact beq_iff_eq.mp hbeq
    have h := receive_preserves_transcriptConsistent auth hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct hT true n msg tsnd hentry r hraw hagree
    simp only [↓reduceIte] at h
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp only [SCKAScheme.recvAUpdate, hkey] at hzc hCPz ⊢
      rw [hzc] at hCPz ⊢
      simp only [hkey, hT.correct] at h
      exact h hCPz

/-- The receive oracle of `party` preserves `CorrectnessInv`. -/
theorem oracleRecv_preserves_correctnessInv
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (party : Bool) :
    QueryImpl.PreservesInv
      (oracleRecv auth irl sampleInitKey party)
      (CorrectnessInv auth ik) := by
  intro n s hs z hz
  cases hzc : z.2.correct
  · exact Or.inl hzc
  rcases hs with hsf | ⟨T, hT⟩
  · cases party
    · rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
        ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, -, rfl⟩
      · simp [hsf] at hzc
      · cases hzc
      · rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
          simp [SCKAScheme.recvBUpdate, hkey, hsf] at hzc
    · rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
        ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, -, rfl⟩
      · simp [hsf] at hzc
      · cases hzc
      · rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
          simp [SCKAScheme.recvAUpdate, hkey, hsf] at hzc
  · exact Or.inr ⟨T, oracleRecv_preserves_transcriptConsistent auth irl sampleInitKey
      hHdrCorrect hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc⟩

end MLKEMBraid
