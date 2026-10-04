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
    let s' := recvSuccessor s party r (msg.epoch - 1)
    (ControlInv s' ∧ StatePairInv s') → TranscriptConsistent auth ik T s' := by
  dsimp only
  -- The receiver keeps its local payload invariant, never lowers its epoch or completed
  -- epoch, and outputs only the transcript key of its next completed epoch.
  have hLocalNew : LocalPayloadInv auth ik T r.state :=
    (receive_recorded_payload auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct hT
      party n msg tsnd hmsg).1 r hr hOutputs
  have hedge := ReceiveEdge.of_eq_ok auth hr
  have hmono : (s.stateAt party).epoch ≤ r.state.epoch := hedge.epoch_le.1
  have hpos := hT.control.epochKnowledge.keyPrefix.pos party
  have hcompMono := hedge.completedEpoch_mono hpos
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
  let s' := recvSuccessor s party r (msg.epoch - 1)
  have hmonos (who : Bool) : (s.stateAt who).epoch ≤ (s'.stateAt who).epoch ∧
      (s.stateAt who).completedEpoch ≤ (s'.stateAt who).completedEpoch := by
    dsimp only [s']
    simp only [stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who; simpa only [↓reduceIte] using And.intro hmono hcompMono
    · simp only [if_neg hwho]; exact ⟨le_rfl, le_rfl⟩
  have hLocal (who : Bool) : LocalPayloadInv auth ik T (s'.stateAt who) := by
    dsimp only [s']
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · exact hLocalNew
    · exact hT.local auth who
  have hKeys (who : Bool) (e : ℕ) :
      s'.keysAt who e = if 0 < e ∧ e ≤ (s'.stateAt who).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e) else none := by
    have hK : s.keysAt who e = if 0 < e ∧ e ≤ (s.stateAt who).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e) else none := hT.keys who e
    dsimp only [s']
    rw [keysAt_recvSuccessor, stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who
      simp only [↓reduceIte]
      rcases hcomp with ⟨hnone, hceq⟩ | ⟨t, key, hkey, ht, hceq⟩
      · rw [hnone, hceq]
        exact hK
      · simp only [hkey, hceq]
        by_cases het : e = t
        · subst het
          obtain ⟨-, -, es', ct1', k', -, hc', -, hk'⟩ := hkeyFact e key hkey
          rw [Function.update_self, if_pos ⟨by omega, le_refl e⟩, hc']
          exact congrArg some hk'
        · rw [Function.update_of_ne het, hK]
          by_cases h1 : 0 < e ∧ e ≤ (s.stateAt party).completedEpoch
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1, if_neg (by omega)]
    · simpa only [if_neg hwho] using hK
  rintro ⟨hC', hP'⟩
  refine ⟨by simpa only [correct_recvSuccessor] using hT.correct, hC', hP',
    hT.keypair_zero, hT.encaps_zero, ?_, ?_, hLocal true, hLocal false, ?_, hKeys⟩
  · intro e pk sk hk
    obtain ⟨h0, hle⟩ := hT.keypair e pk sk hk
    refine ⟨h0, ?_⟩
    rw [← GameState.stateAt_generator] at hle ⊢
    exact hle.trans (hmonos _).1
  · intro e encapsState ct1 key hc
    obtain ⟨h0, hle, pk, sk, hkp, hdec⟩ := hT.encaps e encapsState ct1 key hc
    refine ⟨h0, ?_, pk, sk, hkp, fun hle' => ?_⟩
    · rw [← GameState.stateAt_encapsulator] at hle ⊢
      exact hle.trans (hmonos _).2
    · rw [← GameState.stateAt_generator] at hdec hle'
      rw [stateAt_recvSuccessor] at hle'
      by_cases howner : decide (e % 2 = 1) = party
      · rw [if_pos howner] at hle'
        rw [howner] at hdec
        rcases hcomp with ⟨-, hceq⟩ | ⟨t, k', hkey, ht, hceq⟩
        · exact hdec (hceq ▸ hle')
        · by_cases het : e = t
          · subst het
            obtain ⟨pk', sk', es', ct1', k'', hkp', hc', hdec', -⟩ := hkeyFact e k' hkey
            rw [hkp] at hkp'
            rw [hc] at hc'
            cases hkp'
            cases hc'
            exact hdec'
          · exact hdec (by omega)
      · rw [if_neg howner] at hle'
        exact hdec hle'
  · intro who n' msg' tsnd' hmsg'
    apply hT.messages who n' msg' tsnd'
    exact (congrFun (messagesAt_recvSuccessor s party who r (msg.epoch - 1)) n').symm.trans hmsg'

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
  have hCPz : ControlInv z.2 ∧ StatePairInv z.2 := by
    cases party
    · exact correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (ORecvB (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    · exact correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (ORecvA (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
  rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
    ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
  · exact hT
  · cases hzc
  have hagree : ∀ e key, r.outputKey = some (e, key) → s.keysAt (!party) e = some key := by
    intro e key hkey
    obtain ⟨-, -, _, _, _, _, _, -, -, -, hpeer⟩ :=
      receive_recorded_output auth hCt2Correct hT party n msg tsnd hentry r hraw e key hkey
    rw [recvUpdate_correct, hkey] at hzc
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hzc
    obtain ⟨⟨-, hcons⟩, -⟩ := hzc
    rcases hcons with hnone | hbeq
    · simp [hpeer] at hnone
    · exact beq_iff_eq.mp hbeq
  rw [recvUpdate_eq_successor_of_correct s party tsnd r (msg.epoch - 1) hT.correct hzc] at hCPz ⊢
  exact receive_preserves_transcriptConsistent auth hHdrCorrect hEkCorrect hCt1Correct
    hCt2Correct hT party n msg tsnd hentry r hraw hagree hCPz

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
  · rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, -, rfl⟩
    · simp [hsf] at hzc
    · cases hzc
    · rw [recvUpdate_correct] at hzc
      rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;> simp [hkey, hsf] at hzc
  · exact Or.inr ⟨T, oracleRecv_preserves_transcriptConsistent auth irl sampleInitKey
      hHdrCorrect hEkCorrect hCt1Correct hCt2Correct hT party n z hz hzc⟩

end MLKEMBraid
