/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.RecordedPayload

/-!
# Receives preserve the correctness invariant

A successful receive of a recorded message keeps the game state consistent with the same
transcript when any output key agrees with the peer's recorded key for that epoch. A refusal
or a key disagreement clears the correctness flag. Thus the receive oracles preserve
`CorrectnessInv`.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

private theorem receive_epoch_mono
    [DecidableEq P.Sym]
    (st : State P AuthState) (msg : Message P.Sym)
    (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    st.epoch ≤ r.state.epoch := by
  cases st <;> simp only [receive] at hr
  all_goals repeat' split at hr
  all_goals cases hr
  all_goals simp only [State.epoch]
  all_goals omega

private theorem receive_preserves_transcriptConsistent
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
      (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (if party then s.stA else s.stB) msg = .ok r)
    (hOutputs : ∀ e key, r.outputKey = some (e, key) →
      (if party then s.keyB else s.keyA) e = some key) :
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
    (ControlInv s' ∧ StatePairInv s') →
      TranscriptConsistent P auth ik T s' := by
  -- The receiver keeps its local payload invariant, never lowers its epoch or completed
  -- epoch, and outputs only the transcript key of its next completed epoch.
  have hLocalNew : LocalPayloadInv P auth ik T r.state :=
    (receive_recorded_payload P auth hHdrCorrect hEkCorrect hCt1Correct hCt2Correct ik T s hT
      party n msg tsnd hmsg).1 r hr hOutputs
  have hmono : (if party then s.stA else s.stB).epoch ≤ r.state.epoch :=
    receive_epoch_mono P auth _ msg r hr
  have hpos : 0 < (if party then s.stA else s.stB).epoch := by
    have hposA := hT.control.epochKnowledge.keyPrefix.posA
    have hposB := hT.control.epochKnowledge.keyPrefix.posB
    cases party
    · exact hposB
    · exact hposA
  have hstep := (receive_completedEpoch_of_eq_ok P auth _ hpos msg r hr).2
  have hcomp : (r.outputKey = none ∧
        r.state.completedEpoch = (if party then s.stA else s.stB).completedEpoch) ∨
      ∃ t key, r.outputKey = some (t, key) ∧
        t = (if party then s.stA else s.stB).completedEpoch + 1 ∧
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
        decapsEpochKey P t pk sk encapsState ct1 = some (P.kdfOK k t) ∧
        key = P.kdfOK k t := by
    intro t key hout
    obtain ⟨-, -, pk, sk, encapsState, ct1, k, hkp, hc, hdec, hpeer⟩ :=
      Correctness.Internal.receive_recorded_output P auth hCt2Correct ik T s hT party n msg
        tsnd hmsg r hr t key hout
    have hkey : key = P.kdfOK k t := Option.some.inj ((hOutputs t key hout).symm.trans hpeer)
    subst hkey
    exact ⟨pk, sk, encapsState, ct1, k, hkp, hc, hdec, rfl⟩
  obtain ⟨hcorr, -, -, h0k, h0e, hKeypair, hEncaps, hLocalA, hLocalB, hMessages, hKeys⟩ := hT
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hmono hcomp ⊢
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
  · simp only [↓reduceIte] at hmono hcomp ⊢
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

theorem oracleRecv_preserves_correctnessInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) (party : Bool) :
    QueryImpl.PreservesInv
      (if party then
        SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
       else
        SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey))
      (CorrectnessInv P auth ik) := by
  -- A missing record keeps the state, and a refusal clears the flag. If a successful receive
  -- leaves the flag true, the output key agrees with the peer's key for its epoch, so
  -- `receive_preserves_transcriptConsistent` keeps the new state consistent with the same
  -- transcript.
  let scka := scheme P auth irl sampleInitKey
  cases party
  · intro n s hs z hz
    change z ∈ support ((SCKAScheme.oracleRecvB scka n).run s) at hz
    have hCP : ∀ T, TranscriptConsistent P auth ik T s →
        ControlInv z.2 ∧ StatePairInv z.2 := fun T hT =>
      correctnessImpl_preserves_controlInv_statePairInv P auth irl sampleInitKey
        (ORecvB (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    cases hzc : z.2.correct
    · exact Or.inl hzc
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hs
    rcases hrecv : recvSCKA P auth s.stB msg with
      _ | ⟨keyOpt, treport, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      cases hzc
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    subst stB' treport keyOpt
    rcases hs with hsf | ⟨T, hT⟩
    · rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
        simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
          StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz <;>
        subst z <;>
        simp [hsf] at hzc
    have hCPz := hCP T hT
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      dsimp only at hzc hCPz ⊢
      rw [hzc] at hCPz ⊢
      have h16 := receive_preserves_transcriptConsistent P auth hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik T s hT false n msg tsnd hentry r hraw
        (fun e key h => by simp [hkey] at h)
      simp only [Bool.false_eq_true, ↓reduceIte, hkey, hT.correct] at h16
      exact Or.inr ⟨T, h16 hCPz⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      dsimp only at hzc hCPz ⊢
      have hflag := hzc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hflag
      obtain ⟨⟨-, hcons⟩, -⟩ := hflag
      obtain ⟨-, -, _, _, _, _, _, -, -, -, hpeer⟩ :=
        Correctness.Internal.receive_recorded_output P auth hCt2Correct ik T s hT false n
          msg tsnd hentry r hraw tI key hkey
      simp only [Bool.false_eq_true, ↓reduceIte] at hpeer
      have hconsEq : s.keyA tI = some key := by
        rcases hcons with hnone | hbeq
        · simp [hpeer] at hnone
        · exact beq_iff_eq.mp hbeq
      rw [hzc] at hCPz ⊢
      have h16 := receive_preserves_transcriptConsistent P auth hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik T s hT false n msg tsnd hentry r hraw
        (fun e key' h => by
          rw [hkey] at h
          cases h
          exact hconsEq)
      simp only [Bool.false_eq_true, ↓reduceIte, hkey, hT.correct] at h16
      exact Or.inr ⟨T, h16 hCPz⟩
  · intro n s hs z hz
    change z ∈ support ((SCKAScheme.oracleRecvA scka n).run s) at hz
    have hCP : ∀ T, TranscriptConsistent P auth ik T s →
        ControlInv z.2 ∧ StatePairInv z.2 := fun T hT =>
      correctnessImpl_preserves_controlInv_statePairInv P auth irl sampleInitKey
        (ORecvA (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    cases hzc : z.2.correct
    · exact Or.inl hzc
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hs
    rcases hrecv : recvSCKA P auth s.stA msg with
      _ | ⟨keyOpt, treport, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      cases hzc
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    subst stA' treport keyOpt
    rcases hs with hsf | ⟨T, hT⟩
    · rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
        simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
          StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz <;>
        subst z <;>
        simp [hsf] at hzc
    have hCPz := hCP T hT
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      dsimp only at hzc hCPz ⊢
      rw [hzc] at hCPz ⊢
      have h16 := receive_preserves_transcriptConsistent P auth hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik T s hT true n msg tsnd hentry r hraw
        (fun e key h => by simp [hkey] at h)
      simp only [↓reduceIte, hkey, hT.correct] at h16
      exact Or.inr ⟨T, h16 hCPz⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      dsimp only at hzc hCPz ⊢
      have hflag := hzc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hflag
      obtain ⟨⟨-, hcons⟩, -⟩ := hflag
      obtain ⟨-, -, _, _, _, _, _, -, -, -, hpeer⟩ :=
        Correctness.Internal.receive_recorded_output P auth hCt2Correct ik T s hT true n
          msg tsnd hentry r hraw tI key hkey
      simp only [↓reduceIte] at hpeer
      have hconsEq : s.keyB tI = some key := by
        rcases hcons with hnone | hbeq
        · simp [hpeer] at hnone
        · exact beq_iff_eq.mp hbeq
      rw [hzc] at hCPz ⊢
      have h16 := receive_preserves_transcriptConsistent P auth hHdrCorrect hEkCorrect
        hCt1Correct hCt2Correct ik T s hT true n msg tsnd hentry r hraw
        (fun e key' h => by
          rw [hkey] at h
          cases h
          exact hconsEq)
      simp only [↓reduceIte, hkey, hT.correct] at h16
      exact Or.inr ⟨T, h16 hCPz⟩

end MLKEMBraid
